;; title: Liquid Runner II
;; author: breon knight / technomancy
;; desc: platform puzzler
;; script: fennel
;; input: gamepad
;; saveid: liquid-runner-ii

;;; utility functions

(macro icollect* [iter-tbl value-expr ...] ; from newer fennel
  `(let [tbl# []]
     (each ,iter-tbl
       (tset tbl# (+ (length tbl#) 1) ,value-expr))
     tbl#))

(fn dbg [...] (trace (table.concat [...] " ")))

(fn xykey [x y] (.. x :x y))

(fn last [tbl] (. tbl (length tbl)))

(fn find [tbl x n]
  (match (. tbl (or n 1))
    x (or n 1)
    y (find tbl x (+ n 1))))

(fn find-by [tbl pred]
  "Return the first value for which (pred x) returns truthy."
  (each [k v (pairs tbl)]
    (when (pred v k) (lua "return v, k"))))

(fn group-by [tbl f]
  (let [out {}]
    (each [_ x (ipairs tbl)]
      (let [key (f x)]
        (when (not (. out key)) (tset out key []))
        (table.insert (. out key) x)))
    out))

(fn keys [tbl] (icollect* [k (pairs tbl)] k))

(local neighbors
       [[-1 -1] [0 -1] [1 -1]
        [-1 0] [1 0]
        [-1 1] [0 1] [1 1]])

(fn group [cx cy flag out]
  "Return a table of coordinates for all tiles near cx/cy that all have flag"
  (each [_ [dx dy] (ipairs neighbors)]
    (let [nx (+ cx dx) ny (+ cy dy)]
      (when (and (fget (mget nx ny) flag)
                 (not (find-by out #(match $ [nx ny] true))))
        (table.insert out [nx ny])
        (group nx ny flag out))))
  out)

(fn into [to from]
  (each [k v (pairs from)] (tset to k v))
  to)

(fn pick [tbl] (. tbl (math.random (length tbl))))

(fn pmget [x y] (mget (// x 8) (// y 8)))

(fn clear! [tbl] (while (. tbl 1) (table.remove tbl)))

;;; setup

(local (start-x start-y) (values 16 944))
(local checkpoint-player {:x start-x :y start-y :score 0
                          :w 8 :h 16 :spr 256 :reset 0
                          :carry false})
(local checkpoint-pipes [])
(local checkpoint-enemies [])
(local player {:x start-x :y start-y :w 8 :h 16
               :spr 256 :reset 0 :idle 0 :score 0})

(local active-pipes [])
(local bombs [])
(local enemies [])

;; 4 is still unused
(local flags {:wall 0 :ladder 1 :water 2 :pipe 3
              :ice 5 :spawner 6 :pump 7})

;;; water

(fn pipe-contains? [cx cy {: tiles}]
  (find-by tiles #(match $ [cx cy] true)))

(fn pipe-down [[px py] remaining]
  (assert (< 0 remaining) "pipe goes nowhere!")
  (if (or (fget (mget px (+ py 1)) flags.wall)
          (fget (mget px py) flags.water))
      [px py]
      (pipe-down [px (+ py 1)] (- remaining 1))))

(fn pipe-from-to [tiles flag top-x top-y bottom-x bottom-y]
  (if (= flag flags.pipe)
      [(group top-x top-y flags.water [])
       (pipe-down (last tiles) 99)]
      (let []
        [(group bottom-x bottom-y flags.water [])
         [top-x (- top-y 1)]])))

(fn activate-pipe [cx cy flag]
  (let [tiles (doto (group cx cy flag [])
                (table.sort #(< (. $1 2) (. $2 2))))
        [[top-x top-y]] tiles
        [bottom-x bottom-y] (last tiles)
        [from to] (pipe-from-to tiles flag top-x top-y
                                bottom-x bottom-y)
        key (xykey top-x top-y)
        [from-x from-y to-x to-y] (if (= flag flags.pipe)
                                      [top-x top-y bottom-x bottom-y]
                                      [bottom-x bottom-y top-x top-y])]
    ;; refuse to activate a pipe with no water
    (when (< 0 (length from))
      (sfx 0 nil -1 0 6)
      (tset active-pipes key {: tiles : key : flag : from : to
                              : from-x : from-y : to-x : to-y}))))

(fn toggle-pipe [cx cy flag]
  (match (find-by active-pipes (partial pipe-contains? cx cy))
    pipe (do (tset active-pipes pipe.key nil)
             (sfx -1))
    _ (activate-pipe cx cy flag)))

(fn tile-level [t] (// t 16))

(fn change-level [cx cy diff]
  (if (= (mget cx cy) 0)
      ;; if we're filling empty space, randomize
      ;; which water column to use
      (mset cx cy (pick [16 21]))
      (mset cx cy (+ (mget cx cy) (* diff 16)))))

(fn increase-level-across-row [px py]
  (var (min-x max-x) (values px px))
  (while (not (fget (mget (- min-x 1) py) flags.wall))
    (assert (<= 0 min-x) "draining into open")
    (set min-x (- min-x 1)))
  (while (not (fget (mget (+ max-x 1) py) flags.wall))
    (assert (<= max-x 239) "draining into open")
    (set max-x (+ max-x 1)))
  (for [x min-x max-x]
    (change-level x py 1)))

(fn drain-to [pipe]
  (let [{:to [px py]} pipe]
    (when (and (fget (mget px py) flags.water)
               (= 8 (tile-level (mget px py))))
      (set pipe.to [px (- py 1)]))
    (increase-level-across-row (table.unpack pipe.to))))

(fn flow [pipe]
  (let [rows (group-by pipe.from #(. $ 2))
        [top-y] (doto (keys rows) (table.sort))
        top-tile (mget (table.unpack (. rows top-y 1)))
        level (tile-level top-tile)]
    (each [_ [tx ty] (ipairs (. rows top-y))]
      (change-level tx ty -1))
    (drain-to pipe)
    (when (= level 1)
      (set pipe.from (group pipe.from-x pipe.from-y flags.water []))
      (when (= 0 (length pipe.from))
        (sfx -1)
        (tset active-pipes pipe.key nil)))))

;;; movement logic

(local poffsets
       [[-1 -1] [0 -1] [1 -1]
        [-1 0] [0 0] [1 0]
        [-1 1] [0 1] [1 1]
        [-1 2] [0 2] [1 2]])

(fn touching [x y flag n]
  (match (. poffsets (or n 1))
    [ox oy] (let [cx (+ ox (// x 8)) cy (+ oy (// y 8))]
              (if (fget (mget cx cy) flag)
                  [cx cy]
                  (touching x y flag (+ (or n 1) 1))))))

(fn inside? [{: x : y : w : h} flag]
  (or (fget (mget (// x 8) (// y 8)) flag)
      (fget (mget (// (+ x w -1) 8) (// y 8)) flag)
      (fget (mget (// x 8) (// (+ y 7) 8)) flag)
      (fget (mget (// (+ x w -1) 8) (// (+ y 7) 8)) flag)
      (fget (mget (// x 8) (// (+ y h -1) 8)) flag)
      (fget (mget (// (+ x w -1) 8) (// (+ y h -1) 8)) flag)))

(fn stand-on? [{: x : y : w : h} flag]
  (or (fget (mget (// x 8) (// (+ y h) 8)) flag)
      (fget (mget (// (+ x w -1) 8) (// (+ y h) 8)) flag)))

(fn up-ok? [player]
  (or (inside? player flags.ladder)
      (fget (mget (// player.x 8) (+ (// player.y 8) 1))
            flags.water)
      (fget (mget (// player.x 8) (// (+ player.y player.h -1) 8))
            flags.ice)))

(fn down-ok? [player]
  (or (inside? player flags.water)
      ;; if you're on a ladder, you can go down if
      ;; it doesn't put you inside ice level
      (and (or (inside? player flags.ladder)
               (stand-on? player flags.ladder))
           (or (not (stand-on? player flags.ice))
               (< (tile-level (pmget player.x (+ player.y player.h -1)))
                  (- 8 (math.fmod player.y 8)))))))

;;; enemies

(fn reset []
  (sync 4 1 false)
  (into player checkpoint-player)
  (each [k (pairs active-pipes)]
    (tset active-pipes k nil))
  (each [_ [px py flag] (pairs checkpoint-pipes)]
    (activate-pipe px py flag))
  (each [i [ex ey] (ipairs checkpoint-enemies)]
    (let [e (. enemies i)]
      (set (e.x e.y) (values ex ey))))
  (set player.reset -100)
  (set player.msg nil))

(fn enemy-lr [e]
  (let [{: x : y} e]
    (set e.x (+ e.x e.dx))
    (when (inside? e flags.wall)
      (set (e.x e.dx) (values x (- e.dx))))))

(fn enemy-up-down [e]
  (let [{: x : y} e]
    (set e.y (+ e.y e.dy))
    (when (inside? e flags.wall)
      (set (e.y e.dy) (values y (- e.dy))))))

(fn enemy-pursue-first-choice [e dx dy]
  (let [more-y? (< (math.abs dx) (math.abs dy))]
    (if (and (inside? e flags.ladder) (not (stand-on? e flags.wall)) more-y?)
        (if (< 0 dy) :down :up)
        (and (inside? e flags.ladder) (< dy 0) more-y?) :up
        (if (< 0 dx) :right :left))))

(fn enemy-pursue-second-choice [e dx dy c1]
  (if (or (= c1 :up) (= c1 :down))
      (if (< 0 dx) :right :left)
      (inside? e flags.ladder)
      (if (< 0 dy) :down :up)
      (and (stand-on? e flags.ladder) (< 0 dy))
      :down
      ;; else
      (if (< 0 dx) :right :left)))

;; movement decisions are only ever made on cell boundaries
(fn enemy-move [dx dy pursue]
  (fn [e]
    (let [{: x : y} e]
      (set [e.x e.y] [(+ e.x dx) (+ e.y dy)])
      (when (and (= (/ e.x 8) (// e.x 8)) (= (/ e.y 8) (// e.y 8)))
        (set e.update pursue))
      (when (inside? e flags.wall)
        (set [e.x e.y] [x y])
        (pursue e true))
      (when (and (not (stand-on? e flags.wall))
                 (not (stand-on? e flags.ladder))
                 (not (inside? e flags.ladder)))
        ;; gravity
        (set e.y (+ e.y 1))))))

(fn enemy-pursue [e ?retry]
  (let [dx (- player.x e.x)
        dy (- player.y e.y)
        c1 (enemy-pursue-first-choice e dx dy)
        c2 (enemy-pursue-second-choice e dx dy c1)]
    (match (if ?retry c2 c1)
      :left (set e.update (enemy-move -1 0 enemy-pursue))
      :right (set e.update (enemy-move 1 0 enemy-pursue))
      :up (set e.update (enemy-move 0 -1 enemy-pursue))
      :down (set e.update (enemy-move 0 1 enemy-pursue)))))

(fn ded []
  (set player.ded (+ player.ded 1))
  (print "ouch!" 100 (- player.ded 1) 0 false 2)
  (print "ouch!" 100 player.ded 4 false 2)
  (when (< 90 player.ded)
    (reset)
    (set _G.TIC _G.play)))

(fn corner-hit? [{: x : y : w : h} px py]
  (and (<= x px (+ x w)) (<= y py (+ y h))))

(fn enemy-collide [e]
  (when (or (corner-hit? e player.x player.y)
            (corner-hit? e (+ player.x player.w) player.y)
            (corner-hit? e (+ player.x player.w) (+ player.y player.h))
            (corner-hit? e player.x (+ player.y player.h)))
    (set player.ded 0)
    (set _G.TIC ded)))

;;; checkpoints

(fn count-reset []
  (set player.reset (+ player.reset 1))
  (when (= 60 player.reset)
    (reset)))

(fn set-checkpoint [x y]
  (set player.msg "Checkpoint!")
  (set player.msg-count 90)
  (mset (// x 8) (// y 8) 227)
  (sync 4 1 true)
  (into checkpoint-player player)
  (clear! checkpoint-pipes)
  (clear! checkpoint-enemies)
  (each [_ p (pairs active-pipes)]
    (table.insert checkpoint-pipes [p.to-x p.to-y p.flag]))
  (each [_ e (ipairs enemies)]
    (table.insert checkpoint-enemies [e.x e.y])))

;;; general input actions

(fn drop-bomb [sprite]
  (set player.carry false)
  (table.insert bombs {:x player.x :y (+ player.y 8)
                       : sprite :timer 60}))

(fn left-sprite? [s] (<= 288 s 291))
(fn right-sprite? [s] (<= 256 s 259))

;; which player animation frame is next?
(fn next-spr [s dir]
  (if (and (left-sprite? s) (= 1 dir)) 256
      (and (right-sprite? s) (= -1 dir)) 291
      (= 259 s) 256
      (= s 288) 291
      (+ s dir)))

(var t 0)

(fn go [dir]
  (when (= (math.fmod t 5) 0)
    (set player.spr (next-spr player.spr dir)))
  (set player.x (+ player.x dir)))

(fn bomb-in-wall? [{: x : y : carry}]
  (and carry
       (or (fget (mget (// x 8) (- (// y 8) 1)) flags.wall)
           (fget (mget (// (+ x 7) 8) (- (// y 8) 1)) flags.wall))))

(fn input []
  (let [{: x : y} player] ; horizontal
    (when (btn 2) (go -1))
    (when (btn 3) (go 1))
    (when (or (inside? player flags.wall)
              (bomb-in-wall? player))
      (set player.x x)
      (set player.y y)))
  (let [{: x : y} player] ; vertical
    (when (and (btn 0) (up-ok? player))
      (set player.y (+ player.y -1)))
    (when (and (btn 1) (down-ok? player))
      (set player.y (+ player.y +1)))
    ;; undo it if you try to move into a wall
    (when (and (or (inside? player flags.wall)
                   (bomb-in-wall? player))
               (not (inside? {: x : y :w 8 :h 16} flags.ice)))
      (set player.x x)
      (set player.y y)))
  (when (btnp 4) ; pressing Z
    (if player.carry
        (drop-bomb player.carry)
        (do
          (match (touching player.x player.y flags.pipe)
            [cx cy] (toggle-pipe cx cy flags.pipe))
          (match (touching player.x player.y flags.pump)
            [cx cy] (toggle-pipe cx cy flags.pump)))))
  (if (btn 5)
      (count-reset)
      (set player.reset 0))
  (when (btn 6)
    (dbg :xy player.x player.y "     " (// player.x 8) (// player.y 8))
    (when (btnp 5)
      (set (player.x player.y)
           (values (* player.cheat-x 8) (* player.cheat-y 8)))))
  ;; display reset message when idle
  (if (or (btn 0) (btn 1) (btn 2) (btn 3))
      (set player.idle 0)
      (set player.idle (+ player.idle 1))))

;;; update functions

(fn pick-up-bomb [tile]
  (if (= tile 208) (set player.carry 336)
      (= tile 209) (set player.carry 337)))

(fn normal-gravity []
  ;; gravity in air
  (when (and (not (stand-on? player flags.wall))
             (not (stand-on? player flags.ladder))
             (not (inside? player flags.water))
             (not (inside? player flags.ladder)))
    (set player.y (+ player.y 1)))
  ;; gravity in water is weaker
  (when (and (inside? player flags.water)
             (not (inside? player flags.ladder))
             (not (stand-on? player flags.wall))
             (not (inside? player flags.wall))
             (< (math.random) 0.3))
    (set player.y (+ player.y 1))))

;; ice tiles are unique because their collison box
;; doesn't always follow the 8x8 grid
(fn ice-gravity []
  (let [level (tile-level (pmget player.x (+ player.y player.h -1)))]
    (when (and (< level (- 8 (math.fmod player.y 8)))
               (not (inside? player flags.ladder)))
      (set player.y (+ player.y 1)))))

(fn melt [x y] (mset x y (- (mget x y) 8)))

(fn freeze [x y]
  ;; deactivate pipes flowing frozen water
  (each [_ pipe (pairs active-pipes)]
    (when (find-by pipe.from #(match $ [x y] true))
      (tset active-pipes pipe.key nil)))
  (mset x y (+ (mget x y) 8)))

(local bomb-flags {336 flags.ice 337 flags.water})

(fn trigger-bomb [b]
  (let [affected (group (// b.x 8) (// b.y 8)
                        (. bomb-flags b.sprite) [])]
    (each [_ [x y] (pairs affected)]
      (if (= 336 b.sprite)
          (melt x y)
          (freeze x y)))))

(local dialogs
       {"6x131" ["What are you doing here?"
                 "Oh, searching for the alexis
self-destruct code? Awesome.
You've come to the right place."
                 "These flash drives contain anti-labor
propaganda. I'm replacing their data
with something a little more ... spicy."
                 "You can help out the workers' cause
by doing the same if you see any more
of them deeper in the warehouse."]})

(fn draw-dialog [line]
  (rect 2 2 236 38 13)
  (rectb 3 3 234 36 14)
  (spr 368 8 8 0 1 0 0 2 2)
  (print line 28 12 12))

(fn dialog [lines]
  (_G.draw)
  (match (. lines 1)
    line (draw-dialog line)
    nil (set _G.TIC _G.play))
  (when (btnp 4) (table.remove lines 1)))

(fn no-water [msg x y duration]
  #(if (not (fget (mget x y) flags.water)) (values msg duration)))

(local msgs
       {"4x119" "So this is it; the fabled secret warehouse."
        "13x118" "If I swim to that pipe, I can press Z..."
        "20x125" "Maybe I could swim across?"
        "14x133" "What's that shiny thing over there?"
        "20x133" "Oh, a DVD-R full of tax fraud evidence."
        "32x130" "Pressing Z will start and stop the flow."
        "36x132" (no-water "If only I could swim up to reach the ladder."
                           36 133 300)
        "25x107" "Oh wow, an ice bomb."
        "29x127" (no-water "Might need to reset by holding X..." 29 128 600)
        "32x114" "I can use that bomb by pressing Z here."
        "30x120" "And this fire bomb can melt this ice."
        "50x132" "Whoa, better watch out, monsters!"
        "24x74" "Bombs won't stop the monsters."
        "80x102" "Hmm... Looks tricky; better think this thru."
        "74x130" (no-water "Son of a melonh*cker!" 74 132)})

(fn show-msg [cx cy]
  (mset cx cy 0)
  (let [msg (. msgs (xykey cx cy))
        (msg ?duration) (if (= :function (type msg))
                            (msg)
                            msg)]
    (set player.msg-count (or ?duration 120))
    (set player.msg msg)))

(fn win []
  (cls)
  (when (btnp 5)
    (reset)
    (set _G.TIC _G.play))
  (print (.. player.score " points") 150 10 8)
  (print "YOU WIN" 75 75 14 false 3))

(local pickups {228 100 244 500})
(local pickup-replace {228 213 244 0})

(fn handle-special-tiles [x y]
  (let [head-tile (mget (// x 8) (// y 8))
        foot-tile (mget (// x 8) (// (+ y player.h -1) 8))]
    (when (= 226 head-tile)
      (set-checkpoint x y))
    (when (= 255 head-tile)
      (show-msg (// x 8) (// y 8)))
    (when (= 254 head-tile)
      (mset (// x 8) (// y 8) 0)
      (set _G.TIC (partial dialog (into (. dialogs (xykey (// x 8) (// y 8))) []))))
    (when (= 229 head-tile)
      (set _G.TIC win))
    (when (fget foot-tile flags.spawner)
      (pick-up-bomb foot-tile))
    (match (. pickups head-tile)
      points (do (mset (// x 8) (// y 8) (. pickup-replace head-tile))
                 (set player.score (+ player.score points))))
    (match (. pickups foot-tile)
      points (do (mset (// x 8) (// (+ y player.h -1) 8)
                       (. pickup-replace head-tile))
                 (set player.score (+ player.score points))))))

(fn update []
  (if (inside? player flags.ice)
      (ice-gravity)
      (normal-gravity))
  ;; water drains at a slower rate; only every few ticks
  (set t (math.fmod (+ t 1) 20))
  (when (= t 0)
    (each [_ pipe (pairs active-pipes)]
      (flow pipe)))
  (handle-special-tiles player.x player.y)
  (handle-special-tiles (+ player.x player.w -1) player.y)
  ;; bombs
  (each [i b (pairs bombs)]
    (set b.timer (- b.timer 1))
    (when (= 0 b.timer)
      (trigger-bomb b))
    (when (< b.timer -30)
      (tset bombs i nil)))
  ;; enemies
  (each [_ e (pairs enemies)]
    (e.update e)
    (enemy-collide e)))

;; drawing

(local waterfall-tiles [270 271 286 287])

(fn _G.draw []
  (cls)
  (let [x-offset (- player.x 112)
        y-offset (- player.y 64)]
    ;; pipes
    (each [_ p (pairs active-pipes)]
      (for [y p.to-y (. p.to 2)]
        (spr (pick waterfall-tiles)
             (- (* p.to-x 8) x-offset)
             (- (* y 8) y-offset))))
    ;; map
    (map (// x-offset 8) (// y-offset 8) 31 18
         (- (% player.x 8)) (- (% player.y 8)) 0)
    ;; enemies
    (each [_ e (pairs enemies)]
      (let [flip (if (= e.dx -1) 1 0)]
        (spr e.spr (- e.x x-offset) (- e.y y-offset) 0 1 flip 0 2 2)))
    ;; bombs
    (each [_ {: x : y : sprite : timer} (pairs bombs)]
      (let [bx (- x x-offset) by (- y y-offset)]
        (spr sprite bx by 0)
        (when (< timer 0)
          (circ (+ bx 4) (+ by 4) (* timer -0.3)
                (if (= sprite 336) 3 12))))))
  ;; UI things
  (when (or (< 0 player.reset)
            (< 256 player.idle))
    (print "hold x to reset" 9 9 0)
    (print "hold x to reset" 8 8 12))
  (when player.msg
    (rect 0 124 240 12 0)
    (print player.msg 8 128 12)
    (set player.msg-count (- (or player.msg-count 120) 1))
    (when (<= player.msg-count 0)
      (set player.msg nil)))
  ;; player
  (let [pspr (if player.carry ; arms up?
                 (+ player.spr 4)
                 player.spr)]
    (spr pspr 112 64 0 1 0 0 1 2))
  (print (.. "score: " player.score) 170 9 0)
  (print (.. "score: " player.score) 171 8 12)
  (when player.carry
    (spr player.carry 112 56 0)))

(fn _G.play []
  (input)
  (update)
  (_G.draw))

(fn make-enemy [s]
  (match s
    200 {:spr 480 :w 16 :update enemy-lr :dx 1 :dy 0}
    201 {:spr 482 :w 8 :update enemy-pursue :speed 0.5}
    202 {:spr 484 :w 13 :update enemy-lr :dx 0.5 :dy 0}
    203 {:spr 486 :w 12 :update enemy-up-down :dx 0 :dy 1}))

;; scan the map for enemy tiles to add
(for [x 0 240]
  (for [y 0 168]
    (when (= 239 (mget x y))
      (mset x y 0)
      (set (player.cheat-x player.cheat-y) (values x y)))
    (match (make-enemy (mget x y))
      enemy (do
              (each [k v (pairs {:x (* x 8) :y (* y 8) :h 16})]
                (tset enemy k v))
              (table.insert enemies enemy)
              (mset x y 0)))))

;; change the [!] and [?] msg sprites to be invisible
;; we want to be able to see them so we can place them
;; on the map, but we don't want players to see them.

(for [addr (+ 0x4000 (* 254 32)) 0x6000]
  (poke addr 0))

;; write init state to bank in order to allow reset
;; before you hit your first checkpoint
(sync 4 1 true)

(set _G.TIC _G.play)

;; <TILES>
;; 001:5666666f5666666f056666f0056666f0056666f0056666f0056666f0056666f0
;; 002:056666f0056666f0056666f0056666f0056666f0056666f0056666f0056666f0
;; 003:056666f0056666f0056666f0056666f0056666f0056666f05666666f5666666f
;; 004:d000000dddddddddd000000dd000000dd000000dddddddddd000000dd000000d
;; 006:0344442003444420034444200344442003444420034444200344442003444420
;; 007:3444444234444442034444200344442003444420034444200344442003444420
;; 016:0000000000000000000000000000000000000000000000000000000088988998
;; 017:5666666f5666666f056666f0056666f0056666f0056666f0056666f0856666f8
;; 018:056666f0056666f0056666f0056666f0056666f0056666f0056666f0756666f8
;; 019:056666f0056666f0056666f0056666f0056666f0056666f05666666f5666666f
;; 020:d000000dddddddddd000000dd000000dd000000dddddddddd000000dd888889d
;; 021:0000000000000000000000000000000000000000000000000000000098888889
;; 022:0344442003444420034444200344442003444420034444200344442083444428
;; 023:3444444234444442034444200344442003444420034444200344442083444428
;; 024:00000000000000000000000000000000000000000000000000000000bbcbbccb
;; 025:5666666f5666666f056666f0056666f0056666f0056666f0056666f0b56666fb
;; 026:056666f0056666f0056666f0056666f0056666f0056666f0056666f0b56666fb
;; 027:056666f0056666f0056666f0056666f0056666f0056666f05666666f5666666f
;; 028:d000000dddddddddd000000dd000000dd000000dddddddddd000000ddbbbbbcd
;; 029:00000000000000000000000000000000000000000000000000000000cbbbbbbc
;; 030:03444420034444200344442003444420034444200344442003444420b344442b
;; 031:34444442344444420344442003444420034444200344442003444420b344442b
;; 032:0000000000000000000000000000000000000000000000008888998889988888
;; 033:5666666f5666666f056666f0056666f0056666f0056666f0856666f8856666f8
;; 034:056666f0056666f0056666f0056666f0056666f0056666f0856666f8856666f8
;; 035:056666f0056666f0056666f0056666f0056666f0056666f05666666f5666666f
;; 036:d000000dddddddddd000000dd000000dd000000dddddddddd899988dd888888d
;; 037:0000000000000000000000000000000000000000000000008988888889999888
;; 038:0344442003444420034444200344442003444420034444208344442883444428
;; 039:3444444234444442034444200344442003444420034444208344442883444428
;; 040:000000000000000000000000000000000000000000000000bbbbccbbbccbbbbb
;; 041:5666666f5666666f056666f0056666f0056666f0056666f0b56666fbb56666fb
;; 042:056666f0056666f0056666f0056666f0056666f0056666f0b56666fbb56666fb
;; 043:056666f0056666f0056666f0056666f0056666f0056666f05666666f5666666f
;; 044:d000000dddddddddd000000dd000000dd000000ddddddddddbcccbbddbbbbbbd
;; 045:000000000000000000000000000000000000000000000000bcbbbbbbbccccbbb
;; 046:034444200344442003444420034444200344442003444420b344442bb344442b
;; 047:344444423444444203444420034444200344442003444420b344442bb344442b
;; 048:0000000000000000000000000000000000000000888889988888888888888888
;; 049:5666666f5666666f056666f0056666f0056666f0856666f8856666f8856666f8
;; 050:056666f0056666f0056666f0056666f0056666f0856666f8856666f8856666f8
;; 051:056666f0056666f0056666f0056666f0056666f0856666f85666666f5666666f
;; 052:d000000dddddddddd000000dd000000dd000000dddddddddd888888dd888888d
;; 053:0000000000000000000000000000000000000000899988988888888888888888
;; 054:0344442003444420034444200344442003444420834444288344442883444428
;; 055:3444444234444442034444200344442003444420834444288344442883444428
;; 056:0000000000000000000000000000000000000000bbbbbccbbbbbbbbbbbbbbbbb
;; 057:5666666f5666666f056666f0056666f0056666f0b56666fbb56666fbb56666fb
;; 058:056666f0056666f0056666f0056666f0056666f0b56666fbb56666fbb56666fb
;; 059:056666f0056666f0056666f0056666f0056666f0b56666fb5666666f5666666f
;; 060:d000000dddddddddd000000dd000000dd000000ddddddddddbbbbbbddbbbbbbd
;; 061:0000000000000000000000000000000000000000bcccbbcbbbbbbbbbbbbbbbbb
;; 062:0344442003444420034444200344442003444420b344442bb344442bb344442b
;; 063:3444444234444442034444200344442003444420b344442bb344442bb344442b
;; 064:0000000000000000000000000000000088888888888888889999888888888888
;; 065:5666666f5666666f056666f0056666f0856666f8856666f8856666f8856666f8
;; 066:056666f0056666f0056666f0056666f0856666f8856666f8856666f8856666f8
;; 067:056666f0056666f0056666f0056666f0856666f8856666f85666666f5666666f
;; 068:d000000dddddddddd000000dd000000dd888888dddddddddd888888dd888888d
;; 069:0000000000000000000000000000000088898888898888998888888888888888
;; 070:0344442003444420034444200344442083444428834444288344442883444428
;; 071:3444444234444442034444200344442083444428834444288344442883444428
;; 072:00000000000000000000000000000000bbbbbbbbbbbbbbbbccccbbbbbbbbbbbb
;; 073:5666666f5666666f056666f0056666f0b56666fbb56666fbb56666fbb56666fb
;; 074:056666f0056666f0056666f0056666f0b56666fbb56666fbb56666fbb56666fb
;; 075:056666f0056666f0056666f0056666f0b56666fbb56666fb5666666f5666666f
;; 076:d000000dddddddddd000000dd000000ddbbbbbbddddddddddbbbbbbddbbbbbbd
;; 077:00000000000000000000000000000000bbbcbbbbbcbbbbccbbbbbbbbbbbbbbbb
;; 078:03444420034444200344442003444420b344442bb344442bb344442bb344442b
;; 079:34444442344444420344442003444420b344442bb344442bb344442bb344442b
;; 080:0000000000000000000000008888888888888998888888888888888888888888
;; 081:5666666f5666666f056666f0856666f8856666f8856666f8856666f8856666f8
;; 082:056666f0056666f0056666f0856666f8856666f8856666f8856666f8856666f8
;; 083:056666f0056666f0056666f0856666f8856666f8856666f85666666f5666666f
;; 084:d000000dddddddddd000000dd889898dd888888dddddddddd888888dd888888d
;; 085:0000000000000000000000008899888888888988888888888888888888888888
;; 086:0344442003444420034444208344442883444428834444288344442883444428
;; 087:3444444234444442034444208344442883444428834444288344442883444428
;; 088:000000000000000000000000bbbbbbbbbbbbbccbbbbbbbbbbbbbbbbbbbbbbbbb
;; 089:5666666f5666666f056666f0b56666fbb56666fbb56666fbb56666fbb56666fb
;; 090:056666f0056666f0056666f0b56666fbb56666fbb56666fbb56666fbb56666fb
;; 091:056666f0056666f0056666f0b56666fbb56666fbb56666fb5666666f5666666f
;; 092:d000000dddddddddd000000ddbbcbcbddbbbbbbddddddddddbbbbbbddbbbbbbd
;; 093:000000000000000000000000bbccbbbbbbbbbcbbbbbbbbbbbbbbbbbbbbbbbbbb
;; 094:034444200344442003444420b344442bb344442bb344442bb344442bb344442b
;; 095:344444423444444203444420b344442bb344442bb344442bb344442bb344442b
;; 096:0000000000000000888888889888888988888888888888888888888888888888
;; 097:5666666f5666666f856666f8856666f8856666f8856666f8856666f8856666f8
;; 098:056666f0056666f0856666f8856666f8856666f8856666f8856666f8856666f8
;; 099:056666f0056666f0856666f8856666f8856666f8856666f85666666f5666666f
;; 100:d000000dddddddddd999888dd888888dd888888dddddddddd888888dd888888d
;; 101:0000000000000000998888888888988988888888888888888888888888888888
;; 102:0344442003444420834444288344442883444428834444288344442883444428
;; 103:3444444234444442834444288344442883444428834444288344442883444428
;; 104:0000000000000000bbbbbbbbcbbbbbbcbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
;; 105:5666666f5666666fb56666fbb56666fbb56666fbb56666fbb56666fbb56666fb
;; 106:056666f0056666f0b56666fbb56666fbb56666fbb56666fbb56666fbb56666fb
;; 107:056666f0056666f0b56666fbb56666fbb56666fbb56666fb5666666f5666666f
;; 108:d000000ddddddddddcccbbbddbbbbbbddbbbbbbddddddddddbbbbbbddbbbbbbd
;; 109:0000000000000000ccbbbbbbbbbbcbbcbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
;; 110:0344442003444420b344442bb344442bb344442bb344442bb344442bb344442b
;; 111:3444444234444442b344442bb344442bb344442bb344442bb344442bb344442b
;; 112:0000000088888888899888888888888888888888888888888888888888888888
;; 113:5666666f5666666f856666f8856666f8856666f8856666f8856666f8856666f8
;; 114:056666f0856666f8856666f8856666f8856666f8856666f8856666f8856666f8
;; 115:056666f0856666f8856666f8856666f8856666f8856666f85666666f5666666f
;; 116:d000000dddddddddd888888dd888888dd888888dddddddddd888888dd888888d
;; 117:0000000088988988999888888888888888888888888888888888888888888888
;; 118:0344442083444428834444288344442883444428834444288344442883444428
;; 119:3444444234444442834444288344442883444428834444288344442883444428
;; 120:00000000bbbbbbbbbccbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
;; 121:5666666f5666666fb56666fbb56666fbb56666fbb56666fbb56666fbb56666fb
;; 122:056666f0b56666fbb56666fbb56666fbb56666fbb56666fbb56666fbb56666fb
;; 123:056666f0b56666fbb56666fbb56666fbb56666fbb56666fb5666666f5666666f
;; 124:d000000ddddddddddbbbbbbddbbbbbbddbbbbbbddddddddddbbbbbbddbbbbbbd
;; 125:00000000bbcbbcbbcccbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
;; 126:03444420b344442bb344442bb344442bb344442bb344442bb344442bb344442b
;; 127:3444444234444442b344442bb344442bb344442bb344442bb344442bb344442b
;; 128:8889998888888888888888888888888888888888888888888888888888888888
;; 129:5666666f5666666f856666f8856666f8856666f8856666f8856666f8856666f8
;; 130:856666f8856666f8856666f8856666f8856666f8856666f8856666f8856666f8
;; 131:856666f8856666f8856666f8856666f8856666f8856666f85666666f5666666f
;; 132:d899889dddddddddd888888dd888888dd888888dddddddddd888888dd888888d
;; 133:8888888888888888888888888888888888888888888888888888888888888888
;; 134:8344442883444428834444288344442883444428834444288344442883444428
;; 135:3444444234444442834444288344442883444428834444288344442883444428
;; 136:bbbcccbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
;; 137:5666666f5666666fb56666fbb56666fbb56666fbb56666fbb56666fbb56666fb
;; 138:b56666fbb56666fbb56666fbb56666fbb56666fbb56666fbb56666fbb56666fb
;; 139:b56666fbb56666fbb56666fbb56666fbb56666fbb56666fb5666666f5666666f
;; 140:dbccbbcddddddddddbbbbbbddbbbbbbddbbbbbbddddddddddbbbbbbddbbbbbbd
;; 141:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
;; 142:b344442bb344442bb344442bb344442bb344442bb344442bb344442bb344442b
;; 143:3444444234444442b344442bb344442bb344442bb344442bb344442bb344442b
;; 145:5666666f5666666fe56666fee56666fee56666fee56666fed56666fde56666fe
;; 146:e56666fee56666fed56666fde56666fee56666fee56666fed56666fde56666fe
;; 147:e56666fee56666fed56666fde56666fee56666fee56666fe5666666f5666666f
;; 150:e344442ee344442ed344442de344442ee344442ee344442ed344442de344442e
;; 151:3444444234444442d344442de344442ee344442ee344442ed344442de344442e
;; 160:e566667ee5666665d5666666edf66666edef6666edeef666dedddfffeeeedeee
;; 161:eeeedeeeeeeed555dddd5666ede56666ed566666e5666666d566666fe56666fe
;; 162:e56666fe566666fe666666fd66666fee6666feee666feeeefffdddddeeeedeee
;; 163:eeeedeee555edeee6665eddd66666eee666665ee666666fef66666fde56666fe
;; 164:eeeedeee5555555566666666666666666666666666666666ffffffffeeeedeee
;; 165:deeeeeedddddddddd666666dd666666dd666666ddddddddddffffffddeeeeeed
;; 166:e346442ee444444ee44dd44ee4dddf4ee4dddf4ee44ff44ee444444eeeeeeeee
;; 176:05666670056666650066666600f66666000666660000f666000000ff00000000
;; 177:0000000000000555000056660005666600566666005666660566666f056666f0
;; 178:056666f0566666f0666666f0666666f066666f006666f000ffff000000000000
;; 179:000000005500000066650000666660006666650066666600f66666f0056666f0
;; 180:000000005555555566666666666666666666666666666666ffffffff00000000
;; 181:d000000dddddddddd666666dd666666dd666666ddddddddddffffffdd000000d
;; 196:056666f05555555566666666666666666666666666666666ffffffff056666f0
;; 200:0330000030300000000300330333433033033000000330330330033030000000
;; 201:00b000000bb00b0000ddb000bbdd000000dd0000002020000220200002002000
;; 202:0000000000066000000660000006600060006006060ff0600666660066000666
;; 203:000ee00000ecce00040cce000401100004111000040110000011110001111110
;; 208:000230000000200000002300000230000023300000023000d000000eddddeeee
;; 209:000bc0000000b0000000bc00000bc00000bcc000000bc000d000000eddddeeee
;; 210:eeeedefeeeeedeefddddedddedeeeeeeedeeeeeeedeeeeeededdddddeeeedeee
;; 211:eeee6eeeeeee6eeeddd6eddde6eeefeee6eeeefee6eeeefededdddddeeeedeee
;; 212:eeeedeeeeeeedeeeddddefffedeeefeeedeefeeeedeefeeededdddddeeeedeee
;; 213:00ddd00002ddd200022422000224220002244200022222000022200000000000
;; 224:eeeedeeeeeeedeee66ddeddde6eeeeeee6eeeeeeedeeeeeeded66666eeee6eee
;; 225:eeee6eeeeeee6eee66ddeddde6eeeeeee6eeeeeeedeeeeeeded66666eeee6eee
;; 226:0000000000222000002d2000002d0000000d0000000d0000000d0000000d0000
;; 227:0000000000022000000d2200000d4220000d2442000d0224000d0002000d0000
;; 228:00ddd00006ddd600066466000664660006644600066666000066600000000000
;; 229:0000000000000ddd0000deee0000deff0000def60000deff0000deff0000deff
;; 230:00000000ddddddd0eeeeeed0fffffed066fffed0fffffed0ff66fed0fffffed0
;; 231:0033300003444000034440000344400030444000304400004bbbb4004bbbb400
;; 239:0330300330003003300033333000300303303003000000000333330000030000
;; 240:eeeedeeeeeeedeeed66deddde6eeeeeee6eeeeeeedeeeeeeded66666eeeedeee
;; 241:eeeedeeeeeeedeeeddddedddedeeeeeeedeeeeeeedeeeeeededdddddeeeedeee
;; 242:000d0000000d0000000d0000000d0000000d0000000d0000000d00000ddddd00
;; 243:0000000000ccc00000c0ccc000cc0c0c00ccc0c0000d0ccc000d000c000d0000
;; 244:0000000000cddd000bccddd00dbccdd00ddbccd00dddbcc000dddb0000000000
;; 245:000deeee00deeeee0ddddddd0deeeeee0deddddd0dedeeee0deeeeee0deeeeee
;; 246:eeeeedd0eeeeded0ddddeed0eeedeed0ddedeed0ededeed0eeedeed0eeeddd00
;; 247:4bbbb4004bbbb40004bb0040088800000888800008008000080080000ff0ff00
;; 254:0ccccc00cc222cc0ccc22cc0ccc2ccc0ccc2ccc00ccccc000000c000000c0000
;; 255:0ccccc00ccc2ccc0ccc2ccc0ccccccc0ccc2ccc00ccccc000000c000000c0000
;; </TILES>

;; <SPRITES>
;; 000:00bbbbb00bbbbbb00b44e4000b4244400b444400000400000011100000413000
;; 001:00bbbbb00bbbbbb00b44e4000b4244400b444400000400000011100000413000
;; 002:00bbbbb00bbbbbb00b44e4000b4244400b444400000400000011100000413000
;; 003:00bbbbb00bbbbbb00b44e4000b4244400b444400000400000011100000413000
;; 004:0ebbbbb004bbbbb00444e4000442444004444400040440000441100000413000
;; 005:0ebbbbb004bbbbb00444e4000442444004444400040400000441100000413000
;; 006:0ebbbbb004bbbbb00444e4000442444004444400040400000441100000413000
;; 007:0ebbbbb004bbbbb00444e4000442444004444400040400000441100000413000
;; 014:088888800898888008888980088889800889898008a988a008a988a008a88880
;; 015:08898a8008898a800889888008a9888008a9888008a8898008888980088a8980
;; 016:00411000004444e0001110000099900000999000009990000090900000f0ff00
;; 017:00411000004444e0001110000099900000999000009099000090090000f00f00
;; 018:00411000004444e0001110000099900000999000090090000900900008f0ff00
;; 019:00411000004444e0001110000099900000999000009990000090900000f0ff00
;; 020:0011100000111000001110000099900000999000009990000090900000f0ff00
;; 021:0011100000111000001110000099900000999000009099000090090000f00f00
;; 022:0011100000111000001110000099900000999000090090000900900008f0ff00
;; 023:0011100000111000001110000099900000999000009990000090900000f0ff00
;; 030:0888889009888890098888800989a8800989a88008a8a98008a8898008888880
;; 031:088a88800898888008988a80089888a0088a98a0088a98a0088a888008888880
;; 032:0bbbbb000bbbbbb0004e44b0044454b0004444b0000040000001110000031400
;; 033:0bbbbb000bbbbbb0004e44b0044454b0004444b0000040000001110000031400
;; 034:0bbbbb000bbbbbb0004e44b0044454b0004444b0000040000001110000031400
;; 035:0bbbbb000bbbbbb0004e44b0044454b0004444b0000040000001110000031400
;; 036:0bbbbb0e0bbbbbb4004e44b4044454b4004444b4000040400001140000031400
;; 037:0bbbbb0e0bbbbbb4004e44b4044454b4004444b4000040400001140000031400
;; 038:0bbbbb0e0bbbbbb4004e44b4044454b4004444b4000040400001140000031400
;; 039:0bbbbb0e0bbbbbb4004e44b4044454b4004444b4000040400001140000031400
;; 048:000114000e444400000111000009990000099900000999000009090000ff0f00
;; 049:000114000e444400000111000009990000099900000900900009009000ff0f80
;; 050:000114000e444400000111000009990000099900009909000090090000f00f00
;; 051:000114000e444400000111000009990000099900000999000009090000ff0f00
;; 052:0001110000011100000111000009990000099900000999000009090000ff0f00
;; 053:0001110000011100000111000009990000099900000900900009009000ff0f80
;; 054:0001110000011100000111000009990000099900009909000090090000f00f00
;; 055:0001110000011100000111000009990000099900000999000009090000ff0f00
;; 080:0000000000088000079889702223322222233222079889700008800000000000
;; 081:00000000000ff00007988970222bb222222bb22207988970000ff00000000000
;; 112:000000000000333300022222000233330033334400333344003344440033c6c4
;; 113:33200000333300002330000044430000444230004444300044432000c6c30000
;; 128:0033444403334444033344440323444c03234444002304440330004403300bbb
;; 129:444300004444000044440000cc440000444000004440000040000000bbb00000
;; 224:0000000000000000000000033330000303300003003330030000330300000033
;; 225:0000000033300000333300003333000033330033434300333333003033330030
;; 226:00000000000000000000000000022220000b6bb200bbbbb2000bbbbe0ee0dd00
;; 227:000000000000000000000000000000000000000000000000bee00000b0e00000
;; 228:d0d00d000d0d00d00dd0d000d0d0dd000ddd000000d000660000066600dd0363
;; 229:0000000000000000000000000000000000000000000000006000000060000000
;; 230:0000000000000eee000eeeec040e00cc000000c20b000ccc404000cc04000111
;; 231:00000000e0000000ee000000ceee0000ce000000c0e00000c000000010000000
;; 240:0333333333300003300000030000033300003300000333030003300300000000
;; 241:3333033033333300333030330300300303003000330033003300033300000033
;; 242:00e0dddb00bddd0000e0dd00000022000022220000200200002002000bb0bb00
;; 243:b000000000000000000000000000000000000000000000000000000000000000
;; 244:000d066600002e66ddd0066606e6666600000e4e00000f660660066600666666
;; 245:600000006000000060ddd00066e60000e0000000f00000006006600066660000
;; 246:040111110c1101110c1111110400011100000111000001110000111101111111
;; 247:1000000010000000100000001000000010000000100000001011000011110000
;; </SPRITES>

;; <MAP>
;; 001:00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 068:00000000000000000000000000000000000000000000000000001f1f1f1f1f1f1f1f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 069:000000000000000000000000000000000000000000000000004d04545454045404041e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 070:000000000000000000000000000000000000000000000000001e08585808580808581e1f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 071:000000000000000000000000000000000000000000001f000e585858085858585858580e1f4d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 072:0000000000000000000000000000000000001e1e1f1f1f0e000e0e0e0e0e0e4d0e0e0e000e1f1f1f1f3d1e1e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 073:00000000000000000000000000000000001e00000000000000000000000000000000000000000000000000001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 074:00000000000000000000000000000000001f000000000000ff0000000000000000008c0000000000000000001f0000004e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 075:00000000000000000000000000000000001f000d000000000000000000000000000000000000000000001d001e1e1e004e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 076:0000000000000000000000000000000000003d1f1f0e1f1e400e0e0e0e0e0e3d0e0e0e401e1f1f1f1f1f1f0f0000001e404e4e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 077:00000000000000000000000000000000000000000000001e400e00000000000000000e401e4d001f3d1f000f0000000f0000000000000000000000000000000000000000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 078:00000000000000000000000000000000000000000000001e400e00000000000000000e401e001f001f00000f0000001e0f1e0f0858480f40000000000000000000000000003d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 079:00000000000000000000000000000000000000000000001e4000000000000000001d0e401e0e0e0e0e0e0e0e400e400e0e0e0e0e0e0e0e0e4040400e0e0e0e0e0e0e1f1f1f1f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 080:00000000000000000000000000000000000000000000001e4000000000000000401e40401e000e0000000000400f40404040404040404040404040404040404040404040401f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 081:000000000000000000000000000000000000000000000f1e1e3d00000e48480e401e40400e1f000000000000400f00000000000000000000000000000000ac0000004f00001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 082:000000000000000000000000000000000000000000000f1a3a0e00004d48480e404d40400e000000001d0000400f40404040404040404040404040404040404040404040403d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 083:000000000000000000000000000000000000000000000f0a2a0e790e0e190e0e401e401e0e0e0e0e0e0e0e0e0e0e40404040404040404040404040404040404040404040401f2d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 084:00000000000000001e1e1e1e1e1e1e3d1e1e1f1e1e1f1e1e0e1e600000200000401e401e0000000e0e3d0000000e00000000000000000000000000000000ac00000e0e0e0e0e0e0e0e3d1e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 085:000000000000000f0000000000000000000000000000001e0000602d00300000401e401e002e000000000000000e404040404040404040404040404040404040400e00000000000e4040401e0e1e0f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 086:0000000000003d40000000000000000000000000000000000000602d00000e401e1e401e002f000000000000000e404040404040404040404040404040404040400e0000000000004000401e0f1e562d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 087:00000000001e1e1e1e401e1e1e1e1e4d1e1e1e1e1e00001f401e6a0000000e401e00401e400e40000000000e400e0e0e400e000000000000000000000000ac00000e1e400e000000400e401e5858583d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 088:000000001e0000000040000000000000000000001e000000401f1e1e1e1f1e401f004000400e00000000000e400e402e400e4040404040404040404040404040400e3d400e000000000e401e5858583d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 089:000000001e0000000040000000000000000000001e000e00400000000e1e1e401e004000400e790e0e0e190e400e402f400e4040404040404040404040404040400e1e400e000000000e401e5858584d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 090:000000000e000000000000000000000e0e0e40003d000f0040000000000000401e2e40004000600000002000400e400e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e400e1e400e0e790e0e0e401e5858583d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 091:000000000e0000000000000000000e4e4e0e40001e000f1d40000000000000401e2f40004000600000000b4b5b3b400e00000000000000000000000000000000400e4d4000006000000e401e1818180f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 092:0000000000790e0e0e3d0e0e0e190e00000e40001e00001e00401e4000001e1e1e1f1e1e1ec8e888880e00004030401e00000000000000000000000000002e004000004000006000000e401e2929290f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 093:000000000060001e3d00000000300e40400e40001e00001e00401e0000001e000000002d0e886a88880e00000000001e0d000000000000000000000000002f00400f3d4000006000000e401e3838381f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 094:000000000060001f0000000000000e40404d40001e0f001e00401e1e791e1e001000002d000e0e0e0e0e00000000001e0e0e0e3d0e0e0e0e0808081f0e0e0e3d0e0e0e401e88e888883d401e5858583d000e1e1e0e0e0e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 095:0000000000602d000000000040000e40400e40000d0f001e0040000060002d0020001b4a4b3a0000000f1e1e1e1e1e004d002d404f1e580e5808580e004f404040401e401f88e888881e401e5858580f0000000000000e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 096:0000000000600000000000400e000000000000003d2d001e0d40000060000000200020000029001b4b4b4a4a4a4b3b0000002d40001e581f585858581e00000000401e401e886a88881e401e0e1e3d3d0000000000000e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 097:0000000000600000000000400e000000000000000f1f002e401ec888e81e00000b4b2b00002900200000003d00003000000000402d1e1f0e08585858081e000000001e401f1e1e1e1e1e401e0f1f1f0f0000000000000e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 098:0000000000600e0e0e400e0e1f0e0e1f3d0f0f0f0f00002f401ed8886a1e0e000000001b4b4c4b4c4b4b3b3d0000000000000040003d580f585858580808580808581e40001f000000000000001f1f1e0000000000000e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 099:000000000060000e00400e002e00001e0f0f1f0f0f0f0f0f0f0f1f1e1e002d0f2d000020002000200000291e0000000000000040001f580f58083d085858580858082d00001f00000000002e000000001e00bc0000000e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 100:000000000060004d00401e002f001e1e1e000000000000000000000000002d000000000b4b2b000b3b00290e0000000000000000003d580f083d3d0f080808580858580808581f000000002f000000001e00000000000e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 101:000000000060001e000000001e401e001e002e0000000000000000000000000000000000000000002000200f404040404040401e401f1f0e2d1e003d1f1f0e0e1e5858585858581f1f0e0e0e0000000000001d0000001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 102:000000000060001e000000004d401e001e002f0000000000000000000000000000000040000000000b4b2b1f585818081808081e401f1f1f00000000000000001e58585858581e1e40bc4f1e00000000ff40404000001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 103:000000000060001e191e791e1e403d000e400ec88888c80e1f1f40000000000000000e40000000000000001f1a4a2a1e391e1e1e401f3d1f00000000000000001e581e1e1e1e1e404000401e000000000040404000001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 104:00000000006000002000604040401e000e403d190e3d0e0000001f1f1f1f1f1f1f1f1f400000002d0d1e1d1f3000000000000000402d581f0000000000000000004d0000000000404000001e1e88d8880e404040000d1e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 105:00000000006000002000604000001e000e400e390e0e0000000000000000000000001f40004e00003d1e3d1f0000000000000000401f581f00000000000000000000000000000040400000000e8888d81e4000001e1e1e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 106:0000000000600000200060400e4d000000400000000000001d0000000000000000001e4000000000000000000000003d0000400e401f4d1f00000000000000000000000000000040400000000e0e190e1e4000000f000000000000000000000000000000005e6e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 107:00000000006000002000604000000000004000000000000040ff00000000000000001e4000000000000000000000000e1808080e404d1f1f00000000000000000000000000000e40400000000000291e004000000f000000000000000000000000000000005f6f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 108:000000000060000020006040000000000040000000000000400000000000000000001e4000000000000000000000001e291e1e0e401f0e1f000000000000000000000000000e2e40400000000000291e004000000f0000000000000000000000000000402d3d4d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 109:000000000e600000300e6848081e08481e400e000000400e1e1e400e4848480f40001e4000000000000000000000000030000040401f0d1f000000000000000000000000000e2f4040000000000d394040401e1e0f0000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 110:000000000e6a0000000e6a58081e58581e400e0e0e0e0f0e1e1e400e0e0e190f40001e000000000000000000000e400000000040401f1f1f00000000000000000000000000000e401e1e1e1e1e1e0040404000000f0000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 111:0000001f0e0e0e0e4d0e1f1f1e1e1e1e1e401e1e3d1e1e1e1e1e400e0f0f290f40401e000000000000000000000e000000000e40402e002d000000000000000000000000000000400000000000000040404000000f000000000000404040402d065606065606062d40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 112:00001f1f0000000000000000000000000040000000000000001e400e0000300000401e1e3d1e1e1e1e1e1e1e1e1e000000000f40402f001e000000000000000000000000000000400000000000000040404000000f000000000000000000002d585858585808582d40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 113:001f1f000000000000000000000000000040000000000000001e400e0000000000401e000000001e3d000000001e1e3d1e1e1e1e1e1e403d0000000000000000000000000000002d000000000000000f404040400e00000000403d3d3d3d3d2d580858585858582d40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 114:1f1f000000000000000000000000000d0040000d00000000001e400e00000000ff401e000000000e0e000000000000000000001e0000401e0000000000000000000000000000002d000000000000000f404040400e000000004000000000002d585858085808582d40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 115:1f000000008c0000000000000000000e0d400d0e00000000001e400e0000000000401e000000000000000000000000000000001e0000403d0000000000000000002d4000000000400f0f191e1a3a0f0f404040400e000000004000000000002d2d2d2d2d2d2d2d2d40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 116:1f0000000000000000000000000000003d0e0e0000000000001e400e400f0000400f1e0e400e888888c80e40000000000000001e400f1e1e0f0f0f0f2d0f0f000f0e1848080e404040403000200b3b00404040400e0000000040000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 117:000000000000000000000000000000000000000000000000001e400e000e0e0e0e0e0e0e400ed8d8d8d80e40000000000000001e400f000000000000000000001e1e291e2d1f4d40404000000b4b2b00404040400e0000000040000000400000000000000000000040000000003d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 118:00000000000000000000000000ff00000000000000000000001e400e000000000000000e400e3d0e0e0e0e40000000000000001e400f000000000000000000001e0030000e40001e0e0e000000000000404040400e1f1f1e1e1e1e1e1e400000000000000000000040000000003d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 119:00000000ff00000000000000000000000000000000000000000e400e000000000000000e4000000000000040000000000000000e4000000000000000000000008c0000000e0040404040404040404040404040400e0000000000001e00400000000000000000000040000000003d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 120:0e00000000000000000000400e0e0e06560656460e0e0e40400e400e2e00ff00000000004000000000000040000000000000000e400000000000000000000000000000004d400040000000000000400e0e0e0e0e0e0000000000000000400000001e3d3d3d403d3d3d3d3d40403d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 121:0e0e0e0e0e0e0000000000400e003d08085858480e000000400e400e2f0d00401fc38383c30e4000001d00400e3dc585c50e400e400e00000000000000000000000000000e00400e0000000000000e0000000000000000000000000000400000001e00000040000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 122:000e0e0e4d0e0e0e0e0e0e0e0e000e08580808480e000000400e400e1f0e0e3d1fd8d8d8d80e0e0e0e4d0e0e0e0ed898d80e400e400e0e0e1e00004f000e2d0e1e4040404d40000e0000000000000e000000000000000000000000000040000000001e000040000000001e00400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 123:001e58581f581f5858580e0000000e48481808480e000000400e4000000000001e1e1e0e0e0e000000000000000e0e290e0e400e400e0e1e00004f000e1e4d40404040400e00400e0e0e0e190e0e0e0000000000009c0000000000000040000000001e000040000000001e00400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 124:00002d3d4d0f1f2d3d4d0e0000000e1a4a2a0e0e0e000000400e40002e00000000000000000e000000000000000000300000400e400e00000000000e1e404040404040400e00004040401a2a0000000000000e00000000000000000000400000000000000040000000001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 125:000e0d0000000000001d3d000000002000000000ff000000400e40002f00000000000000003d000000000000000000000000400e400000000000008c00000000000000000e4040000000290e0000000000001e1e1e1e1e1e1e1e1e1e1e404040404040000040000000001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 126:000e0e0000000000000e0e00000000200000000000000000404d0e1e1e4000000000400e400e00000000000e400000000000400e400000000000000000000000000000000e00000e0e0e390e000000000000000000000000000000000040000000001e1e0e0e0e4000001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 127:001f1f190f190f190f0f0e0000000030000000400e4d0e0e0e0e00000eff00000000000f400e00000000000e00000000400e0e0e400e40000000000000000000000000000e0e0e0e0000000e00fe2e000000000000000000000000000040000000001e000000004000001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 128:0e1f0030003000300000ff00000e400000400e0e0e000000400000000e0808080818080f404d004e0000400e00000000400e0000400e0e1e0e0e1e000e0e2d1e0f4040402d0000000000000e00002f000000000000000000000000000040000000001e000000004000001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 129:1e4d00000000000000000000000e000000400e0000000000000000000e3d0e0e1e290f0f400e00000000404d0e0e0e4d0e0e0000400e0e2d0e1e0000000e1e40404040400e400000400e000000400e1e1e000000000000000000000000400000000000000000004000001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 130:1f1f00000000000000400e00003d000000400e0000400e0e000e002e00000000ff300000400e0e0e0e0040000000000000000e00400e00000000000000000000000000000e400000000eff0000000e00001e1e1e1e1e1e00000000401f1f1f1f1f40000000000040001e1e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 131:1e1f004e004e004e00400e00000e000000000e000040000e400e002f0000000000000000400e00000e0040000000000000000e004000008c0000000000000000000000000e400000400e000000000e000000000000001f1f1f1f1f1f1f0000001f1e1e1e1e1e1e1e1e1e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 132:1f1f00400040004000400e0000000e0e0e0e4d0e0e400e0e400e0e0e0e0e400040000000ff004f000e00400000000000002eff00400000000000000000000000000000000e400000000e000000000e00000000000000000000000000000000001f1f1f1f1f1f1f1f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 133:001f1f1f1f1f1f1f1f4d0e000000ff0000000000ff40004f400e0000000e400040000000000040000e00400000000000002f0000400e40004e004e00000000001e00000000001f3d0e0e0e0e0e0e0e000000000000000000000000000000000000001f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 134:0000000000000000000e0e00000000000000000000400000401e000000000e0e0e1f1e1e1e4d0e0e0e0e0e0e4808580e0e0e4d0e0e0e0000000000000000000f2d00000000001f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 135:000000000000000000000e0e0e0e0e4d0e0e0e0e0e0e0e0e0f000000000000000000000000000000000000000f0f0f000000000000001f1f1f1f4d1f1f1f1f1e1f1f1f2d1f1f1f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; </MAP>

;; <MAP1>
;; 001:00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 068:00000000000000000000000000000000000000000000000000001f1f1f1f1f1f1f1f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 069:000000000000000000000000000000000000000000000000004d04545454045404041e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 070:000000000000000000000000000000000000000000000000001e08585808580808581e1f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 071:000000000000000000000000000000000000000000001f000e585858085858585858580e1f4d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 072:0000000000000000000000000000000000001e1e1f1f1f0e000e0e0e0e0e0e4d0e0e0e000e1f1f1f1f3d1e1e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 073:00000000000000000000000000000000001e00000000000000000000000000000000000000000000000000001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 074:00000000000000000000000000000000001f000000000000ff000000000000000000000000000000000000001f0000004e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 075:00000000000000000000000000000000001f000d000000000000000000000000000000000000000000001d001e1e1e004e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 076:0000000000000000000000000000000000003d1f1f0e1f1e400e0e0e0e0e0e3d0e0e0e401e1f1f1f1f1f1f0f0000001e404e4e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 077:00000000000000000000000000000000000000000000001e400e00000000000000000e401e4d001f3d1f000f0000000f0000000000000000000000000000000000000000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 078:00000000000000000000000000000000000000000000001e400e00000000000000000e401e001f001f00000f0000001e0f1e0f0858480f40000000000000000000000000003d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 079:00000000000000000000000000000000000000000000001e4000000000000000001d0e401e0e0e0e0e0e0e0e400e400e0e0e0e0e0e0e0e0e4040400e0e0e0e0e0e0e1f1f1f1f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 080:00000000000000000000000000000000000000000000001e4000000000000000401e40401e000e0000000000400f40404040404040404040404040404040404040404040401f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 081:000000000000000000000000000000000000000000000f1e1e3d00000e48480e401e40400e1f000000000000400f00000000000000000000000000000000000000004f00001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 082:000000000000000000000000000000000000000000000f1a3a0e00004d48480e404d40400e000000001d0000400f40404040404040404040404040404040404040404040403d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 083:000000000000000000000000000000000000000000000f0a2a0e790e0e190e0e401e401e0e0e0e0e0e0e0e0e0e0e40404040404040404040404040404040404040404040401f2d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 084:00000000000000001e1e1e1e1e1e1e3d1e1e1f1e1e1f1e1e0e1e600000200000401e401e0000000e0e3d0000000e000000000000000000000000000000000000000e0e0e0e0e0e0e0e3d1e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 085:000000000000000f0000000000000000000000000000001e0000602d00300000401e401e002e000000000000000e404040404040404040404040404040404040400e00000000000e4040401e0e1e0f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 086:0000000000003d40000000000000000000000000000000000000602d00000e401e1e401e002f000000000000000e404040404040404040404040404040404040400e0000000000004000401e0f1e562d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 087:00000000001e1e1e1e401e1e1e1e1e4d1e1e1e1e1e00001f401e6a0000000e401e00401e400e40000000000e400e0e0e400e0000000000000000000000000000000e1e400e000000400e401e5858583d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 088:000000001e0000000040000000000000000000001e000000401f1e1e1e1f1e401f004000400e00000000000e400e402e400e4040404040404040404040404040400e3d400e000000000e401e5858583d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 089:000000001e0000000040000000000000000000001e000e00400000000e1e1e401e004000400e790e0e0e190e400e402f400e4040404040404040404040404040400e1e400e000000000e401e5858584d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 090:000000000e000000000000000000000e0e0e40003d000f0040000000000000401e2e40004000600000002000400e400e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e400e1e400e0e790e0e0e401e5858583d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 091:000000000e0000000000000000000e4e4e0e40001e000f1d40000000000000401e2f40004000600000000b4b5b3b400e00000000000000000000000000000000400e4d4000006000000e401e1818180f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 092:0000000000790e0e0e3d0e0e0e190e00000e40001e00001e00401e4000001e1e1e1f1e1e1ec8e888880e00004030401e00000000000000000000000000002e004000004000006000000e401e2929290f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 093:000000000060001e3d00000000300e40400e40001e00001e00401e0000001e000000002d0e886a88880e00000000001e0d000000000000000000000000002f00400f3d4000006000000e401e3838381f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 094:000000000060001f0000000000000e40404d40001e0f001e00401e1e791e1e001000002d000e0e0e0e0e00000000001e0e0e0e3d0e0e0e0e0808081f0e0e0e3d0e0e0e401e88e888883d401e5858583d000e1e1e0e0e0e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 095:0000000000602d000000000040000e40400e40000d0f001e0040000060002d0020001b4a4b3a0000000f1e1e1e1e1e004d002d404f1e580e5808580e004f404040401e401f88e888881e401e5858580f0000000000000e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 096:0000000000600000000000400e000000000000003d2d001e0d40000060000000200020000029001b4b4b4a4a4a4b3b0000002d40001e581f585858581e00000000401e401e886a88881e401e0e1e3d3d0000000000000e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 097:0000000000600000000000400e000000000000000f1f002e401ec888e81e00000b4b2b00002900200000003d00003000000000402d1e1f0e08585858081e000000001e401f1e1e1e1e1e401e0f1f1f0f0000000000000e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 098:0000000000600e0e0e400e0e1f0e0e1f3d0f0f0f0f00002f401ed8886a1e0e000000001b4b4c4b4c4b4b3b3d0000000000000040003d580f585858580808580808581e40001f000000000000001f1f1e0000000000000e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 099:000000000060000e00400e002e00001e0f0f1f0f0f0f0f0f0f0f1f1e1e002d0f2d000020002000200000291e0000000000000040001f580f58083d085858580858082d00001f00000000002e000000001e00000000000e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 100:000000000060004d00401e002f001e1e1e000000000000000000000000002d000000000b4b2b000b3b00290e0000000000000000003d580f083d3d0f080808580858580808581f000000002f000000001e00000000000e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 101:000000000060001e000000001e401e001e002e0000000000000000000000000000000000000000002000200f404040404040401e401f1f0e2d1e003d1f1f0e0e1e5858585858581f1f0e0e0e0000000000001d0000001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 102:000000000060001e000000004d401e001e002f0000000000000000000000000000000040000000000b4b2b1f585818081808081e401f1f1f00000000000000001e58585858581e1e40004f1e00000000ff40404000001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 103:000000000060001e191e791e1e403d000e400ec88888c80e1f1f40000000000000000e40000000000000001f1a4a2a1e391e1e1e401f3d1f00000000000000001e581e1e1e1e1e404000401e000000000040404000001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 104:00000000006000002000604040401e000e403d190e3d0e0000001f1f1f1f1f1f1f1f1f400000002d0d1e1d1f3000000000000000402d581f0000000000000000004d0000000000404000001e1e88d8880e404040000d1e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 105:00000000006000002000604000001e000e400e390e0e0000000000000000000000001f40004e00003d1e3d1f0000000000000000401f581f00000000000000000000000000000040400000000e8888d81e4000001e1e1e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 106:0000000000600000200060400e4d000000400000000000001d0000000000000000001e4000000000000000000000003d0000400e401f4d1f00000000000000000000000000000040400000000e0e190e1e4000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 107:00000000006000002000604000000000004000000000000040ff00000000000000001e4000000000000000000000000e1808080e404d1f1f00000000000000000000000000000e40400000000000291e004000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 108:000000000060000020006040000000000040000000000000400000000000000000001e4000000000000000000000001e291e1e0e401f0e1f000000000000000000000000000e2e40400000000000291e004000000f0000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 109:000000000e600000300e6848081e08481e400e000000400e1e1e400e4848480f40001e4000000000000000000000000030000040401f0d1f000000000000000000000000000e2f4040000000000d394040401e1e0f0000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 110:000000000e6a0000000e6a58081e58581e400e0e0e0e0f0e1e1e400e0e0e190f40001e000000000000000000000e400000000040401f1f1f00000000000000000000000000000e401e1e1e1e1e1e0040404000000f0000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 111:0000001f0e0e0e0e4d0e1f1f1e1e1e1e1e401e1e3d1e1e1e1e1e400e0f0f290f40401e000000000000000000000e000000000e40402e002d000000000000000000000000000000400000000000000040404000000f000000000000404040402d065606065606062d40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 112:00001f1f0000000000000000000000000040000000000000001e400e0000300000401e1e3d1e1e1e1e1e1e1e1e1e000000000f40402f001e000000000000000000000000000000400000000000000040404000000f000000000000000000002d585858585808582d40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 113:001f1f000000000000000000000000000040000000000000001e400e0000000000401e000000001e3d000000001e1e3d1e1e1e1e1e1e403d0000000000000000000000000000002d000000000000000f404040400e00000000403d3d3d3d3d2d580858585858582d40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 114:1f1f000000000000000000000000000d0040000d00000000001e400e00000000ff401e000000000e0e000000000000000000001e0000401e0000000000000000000000000000002d000000000000000f404040400e000000004000000000002d585858085808582d40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 115:1f00000000000000000000000000000e0d400d0e00000000001e400e0000000000401e000000000000000000000000000000001e0000403d0000000000000000002d4000000000400f0f191e1a3a0f0f404040400e000000004000000000002d2d2d2d2d2d2d2d2d40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 116:1f0000000000000000000000000000003d0e0e0000000000001e400e400f0000400f1e0e400e888888c80e40000000000000001e400f1e1e0f0f0f0f2d0f0f000f0e1848080e404040403000200b3b00404040400e0000000040000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 117:000000000000000000000000000000000000000000000000001e400e000e0e0e0e0e0e0e400ed8d8d8d80e40000000000000001e400f000000000000000000001e1e291e2d1f4d40404000000b4b2b00404040400e0000000040000000400000000000000000000040000000003d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 118:00000000000000000000000000ff00000000000000000000001e400e000000000000000e400e3d0e0e0e0e40000000000000001e400f000000000000000000001e0030000e40001e0e0e000000000000404040400e1f1f1e1e1e1e1e1e400000000000000000000040000000003d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 119:00000000ff00000000000000000000000000000000000000000e400e000000000000000e4000000000000040000000000000000e400000000000000000000000000000000e0040404040404040404040404040400e0000000000001e00400000000000000000000040000000003d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 120:0e00000000000000000000400e0e0e06560656460e0e0e40400e400e2e00ff00000000004000000000000040000000000000000e400000000000000000000000000000004d400040000000000000400e0e0e0e0e0e0000000000000000400000001e3d3d3d403d3d3d3d3d40403d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 121:0e0e0e0e0e0e0000000000400e003d08085858480e000000400e400e2f0d00401fc38383c30e4000001d00400e3dc585c50e400e400e00000000000000000000000000000e00400e0000000000000e0000000000000000000000000000400000001e00000040000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 122:000e0e0e4d0e0e0e0e0e0e0e0e000e08580808480e000000400e400e1f0e0e3d1fd8d8d8d80e0e0e0e4d0e0e0e0ed898d80e400e400e0e0e1e00004f000e2d0e1e4040404d40000e0000000000000e000000000000000000000000000040000000001e000040000000001e00400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 123:001e58581f581f5858580e0000000e48481808480e000000400e4000000000001e1e1e0e0e0e000000000000000e0e290e0e400e400e0e1e00004f000e1e4d40404040400e00400e0e0e0e190e0e0e000000000000000000000000000040000000001e000040000000001e00400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 124:00002d3d4d0f1f2d3d4d0e0000000e1a4a2a0e0e0e000000400e40002e00000000000000000e000000000000000000300000400e400e00000000000e1e404040404040400e00004040401a2a0000000000000e00000000000000000000400000000000000040000000001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 125:000e0d0000000000001d3d000000002000000000ff000000400e40002f00000000000000003d000000000000000000000000400e400000000000000000000000000000000e4040000000290e0000000000001e1e1e1e1e1e1e1e1e1e1e404040404040000040000000001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 126:000e0e0000000000000e0e00000000200000000000000000404d0e1e1e4000000000400e400e00000000000e400000000000400e400000000000000000000000000000000e00000e0e0e390e000000000000000000000000000000000040000000001e1e0e0e0e4000001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 127:001f1f190f190f190f0f0e0000000030000000400e4d0e0e0e0e00000eff00000000000f400e00000000000e00000000400e0e0e400e40000000000000000000000000000e0e0e0e0000000e00002e000000000000000000000000000040000000001e000000004000001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 128:0e1f0030003000300000ff00000e400000400e0e0e000000400000000e0808080818080f404d004e0000400e00000000400e0000400e0e1e0e0e1e000e0e2d1e0f4040402d0000000000000e00002f000000000000000000000000000040000000001e000000004000001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 129:1e4d00000000000000000000000e000000400e0000000000000000000e3d0e0e1e290f0f400e00000000404d0e0e0e4d0e0e0000400e0e2d0e1e0000000e1e40404040400e400000400e000000400e1e1e000000000000000000000000400000000000000000004000001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 130:1f1f00000000000000400e00003d000000400e0000400e0e000e002e00000000ff300000400e0e0e0e0040000000000000000e00400e00000000000000000000000000000e400000000eff0000000e00001e1e1e1e1e1e00000000401f1f1f1f1f40000000000040001e1e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 131:1e1f004e004e004e00400e00000e000000000e000040000e400e002f0000000000000000400e00000e0040000000000000000e00400000000000000000000000000000000e400000400e000000000e000000000000001f1f1f1f1f1f1f0000001f1e1e1e1e1e1e1e1e1e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 132:1f1f00400040004000400e0000000e0e0e0e4d0e0e400e0e400e0e0e0e0e400040000000ff004f000e00400000000000002eff00400000000000000000000000000000000e400000000e000000000e00000000000000000000000000000000001f1f1f1f1f1f1f1f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 133:001f1f1f1f1f1f1f1f4d0e000000ff0000000000ff40004f400e0000000e400040000000000040000e00400000000000002f0000400e40004e004e00000000001e00000000001f3d0e0e0e0e0e0e0e000000000000000000000000000000000000001f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 134:0000000000000000000e0e00000000000000000000400000401e000000000e0e0e1f1e1e1e4d0e0e0e0e0e0e4808580e0e0e4d0e0e0e0000000000000000000f2d00000000001f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 135:000000000000000000000e0e0e0e0e4d0e0e0e0e0e0e0e0e0f000000000000000000000000000000000000000f0f0f000000000000001f1f1f1f4d1f1f1f1f1e1f1f1f2d1f1f1f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; </MAP1>

;; <SFX>
;; 000:00e000f0029003a003b053b074cf85ce96dd97eca8eba9fa9af99af89bf99d0e9d0d8c0c8c0c8b0c7b0d7c0d6d0f6e006e016e036e036c046a056a0614300f0f0f0f
;; </SFX>

;; <FLAGS>
;; 000:0090909020001818000000000000000040d0d0d0604058580212121222021a1a40d0d0d0604058580212121222021a1a40d0d0d0604058580212121222021a1a40d0d0d0604058580212121222021a1a40d0d0d0604058580212121222021a1a40d0d0d0604058580212121222021a1a40d0d0d0604058580212121222021a1a40d0d0d0604058581212121232121a1a009090900000181800000000000000009090909090a0180000000000000000009090909090a00000000000000000000000000000900000000000000000000000040410101000000000000000000000001010000000000000000000000000000010100000000000000000000000000000
;; </FLAGS>

;; <PALETTE>
;; 000:0400005d275db13e53ef7d57ffcd75a7f07038b76425717929366f3b5dc941a6f673eff7f4f4f494b0c2566c86333c57
;; </PALETTE>

;; <COVER>
;; 000:b24100007494648393160f00880077000012ffb0e45445353414055423e2033010000000129f40402000ff00c2000000000f0088007840000065c668837b46490b2c33c3754f4f4f9263f6b3d59c37fe7f7a0f07521797fed775ffdc571be335d572d500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080ff001080c18203081c0020e0e00282070c1c00e0d023c9841b2a5cb881b2e3c88017227448f051e14d8223428439c194a1c499113e6c19d23666c789075e08b983f32b499c3b76cc796337ed4a962122cc9804346dc09b391625f984b46008a4510800103437a7cba95f665dfa559ba34dac0708858824d12185b51372adc9903de85fa41dc26d7b06108dd9bb03facc39b1d320e3ae7b0f5c1cb250f2d4a40422543a627963e596253e267cf511f453c33f277c2ba993b8e7ce9bf21478e912f4edc84f3e1c5c39d53b67ae93f68e1d6112f649bab903e61ddb38a0d0e4930ca6d82b707ceacf856bd67efbbe24cba4dd4f0cca4dfa647cd363b365f8dd3b3fff5c9d6fdab5ed96bcbd5ae973c3bfdee4f5b241c2f133cf2c443138eafc4d7f0c4a00a45a29e66b9087fd045041060d256a528a7d3490ad7719387025815517f9d969fdc640d35f8918f31885550011e2590e9870548801a8601b860cb8704c8f26547261053d9873938115d8000b6e0a58205d8504090421961e98802290082924e58ab9c5f1d2530635d1a88335a8c466934e29a4279b56986f9a8c2ef8a029910cb8862a943e793005834ae820410b09e84057957e69c5609c09b9972998729944654761957ad0a47187d59577a1e4879c46712937e19f56e9b46f9b562a66548d6eb919eb9e5e29304a996ea9d3eb939ae84269a34ec667629ea65a77edff987a19f9eba84596a8137da9eae4147f390094a9af7e9a3ba2942a280160ad46485923ba0a8aa6254e06aa7ce0ba06c984af86aa4be66194960b64a5b2beda825ea12127cb678eb6b4025d8b91f85b61995e34aaa2857ebbcca796014b33e3650d4589197d0dc6c1e18999c6052178ee9bdc5abe295721e88c07f84f644ff568701fb608a7ed92aa79b7ad91ce718cfd59542ba7241ac486b47238542fbc3d98713357a1f08c02d7b0af722345b1a7c15aec413683520d3474ce3d68106ec8256ccfadc3f595b3b16800e9949fc84b4594317a5727c5f3da1a456536d263689535971b2d6edac1538580c9df42f6cf59d5457db47dddf907e618d0739d36f6ffd3730d68e1a7ddad58d4d2050ee370ea8365c7d2e98a3ed833e6ed6529bada714ef616e8350e6959b0531ec635d8b2869a59e5499e19d9eaa3356e6064afaea41ce7571c50d8e7a18ef5d4d2ab7ea12ae1b7ae0cffe2cfce65bde7d9668cbfe3bf2cbb5a78b75568714803a7f7bdd27b5fd7f4f96117903dd77f7f9437c2e974fcbf4e1b15be1750edccc51bf775affe77cee3cc0ffbcbe7df7fbcf5ffcfcf3cfe4be77bb2f1f42f61cb0b1ad6679c39d5cd61886330206c18ac360620d8614b7029f408571c9950d46a1492d7848622370274c764240f890938f93721384e281cabcede1805a71a70d9466bde42c4f613cc1ae077869b3c55e40610c61601fffa388b3161ae78e13f162a67642c6f95e407d09212a0715714271be25824c684becb67d92e93ca67f5c8e871fa845c92671d88764c2678c87a5cc2e0ee5746c436fe2c87b138d81d5756cc3ac17f815ca26fa052c24736417b7ad3e1a2ca1631b3057f009c3c64a32b78f02cf9a158842c9f1a13a8ee31fdb7ce89fb1f991bf8f9cf8d525f2ffbc0db1509014e2282fb686b2523153832c152415491ac95ae4418704ef020679cbce5af2110553956037f3d041666f88612485223d0695b802ade790d4e565dc193dcde1f7e197d3ad54de6802c7ede52378444cdd42e273986643b885b447e111352b417e21bc7d4c7fdc27d631c1e1f76236e486a664a83ff7c83e0c8d84bce728f828fa4832dbac75f4402c62009fcf5ee35890054d0fe8f8f0a4dcab04777c56e18cf68db30636a1aeb4ee153b097e164a12db7a1dbfc2231981def9ef4f7241096f2de75b4a9e2ac2953def5ac0e9d9cd42eea998b4dd8c45a97d436613989b14d3e0c42853cd6a2390a22bc666378abbc16a25f1406b7aa927597c3b2d862a7d3111aa230a415b52f3bbac7b594206dac65e82349aa5d4342e078337dd1a786b3d633fdb0748f8ceba32d98969408774009000762a8aa8007bca580076d688a3bb8c8a5c636f2784cbf085d150e10ca95569395b522fc1228d1ce55667885dd4c602a31d18174e4b5bca3ef6e2b89538e8573b5354dff2a424b2a52c230b4b1195d476f1a0a9edec633a05dcb8ee0a24cdda2959baccd5ea377c2541cd6e6500bc9090f6d02ebd19a94b4a6c15886795af5d9593a8a7c41fba975783f39e257900ed16c29c01b3e102695d6ad5c4b1d6f6aef3ee025608d355f5d6ffb75db5e144ab39120b0fa4b95d6d61519a1b4507b29b3c8a49e921daf42eca58d1cdb19ea20c0260e4ac2081002e017302b9ae5ae663359004a0b54ba730d4bab55aa7cc41737feb3f5da6004dbb6d6fe7fe3c12601f8836c73e1cea6cdacd481a53379e264920916c94661f97f9c052dce00a4c24edbc8787ce36b2b169f2146ae4364372f57c2213171ec23f3eccc19b33ba93dcc6ed2f4e0ff0c53e6da549db3dd5d4a60bcc08f1b33bbc7599c83339b9cd48a407fc48e0a644b3b88ed2a848ec246402e95fc14de0ff951dac59860f41a68ec4f5a70d9ad7e62ab5b47364b79b5c10874739d42d1652bd73b2bd5649aaf5cb4e85f9ab5c05ea5f9706a3085ca467835fb743674665f320ffaba3835cf67cafb1f306fb459dcc626fefe9dbc676f1b1ec33efdaca5b6b813536a70c9d9127d315c59ed6bd319c2862771ab0871e00b5bdcdc2ed0100e1de3120785b383b57738589c08920573f7ac9ee86eb1edd3197f00568edd327eb502dfae90eb76821bd738e0cca5edc55610ec31187c67d93e1acd2151070081920a7201fdc53aeb2c9348e9b7cdfeffee17302eddde97bc656c5153943066eb0850ccc75ef7939f46c635b139b6a15e4179985c362086a4fdcb6e737e949b593ad45a7fcf970be95f8428e1391a3bc8cbdc3e575683ee1758fba71afc903231d5adc672a7725e22669b79d5e6c6f46bd73990f1029dd9db3dfa4bc0aedfe17ffb55ea6fe33bd55c5f6ef8eb79ed455ab0e509514687b40edf296c854cae9110738bb74eb44cf1621caee47795d59c316c794800f8f69f0cd0eb242df84810597bc71d65d6beeba0aa2bd97ebf976e92018c3648cccec2b07e24c100608aed22f8da6b6e76cd930f26481f715288def2254f79f45c7c12efd396a3d4361e7d2b8f7059902f5cebc7b843f50a7afe1bff4f7afef4f4f0ff9bcc390f046bf6cfadb8e7cb48c653bafc5eb7fdf8f11995f6db97539123debcedeb5115260a77175f5294f67ad1026e00e007f72816081769977d7f14707ef7967775c01208cf5845733a18031c00e00b00c081f1745018428b97711d00028051e97491e87f718970878e6c18e81a08b08128e63d065286d7106911837e31b28aa1687812546eb3348031438638738507af7bf7811828a282b7ea64b7fa79b7817e66f445277488486513667e75d78e7728928e38c77784fb24d75e69c5201132700a58d32786d58d95068168d31ce79d7ce2115768496968132c680c59386e7118611e48f485189c7781425ea6de6873888c03a68c7878ff8b48e84d61bf51b79671f5944ed75c65081d6ef57080c2000b68b68a584f5a38f08628882f11378368e557973280382c33970000a7c61848d33f68d58ba70e65a6c00200e36d47e282484f6414297a55300ab3bb4272d05722885555f28b45257dc8855e07c33575116704d36026eb81222484072c8cd8ca7175931bc80754d83417d6c756075870f7917ab7844db7c007318d89711c7495fe4e74266458444366fb45c82e82353f81173e4866f66558166c33803496db7831400c009d8678668f473946968747c35a1bf8df8235d78419f375f6019451cd3809fe8731b09d09d91f09164fd7a19c41619719d05919ff4b19037219ae79b1f880d5621026b6ff11f87f65394686231f75e5f399f7831c29d29c39fa6649267e82ba68c6ee8d364297b79988949f56f8f131595595f3b294491d43a8759b989c65d18c6387838ea8541f49ca8945ea82982381e67d4959a59e05b06ca4b47b18279a879b3872265b96ce6ef6479416d45e33a69279c11cb4ac80255894899029f4655e793b5189c89139089811975f138e80394e69c15a74752d8384577e39a99245f693e8bd8599a88471947c99404f63d849111d34241580090b9ee4d66f443b77981994590b91a9455ff8ff8201d00300d388b7be8b387110656538996998d66685884a4394d640e7601ab9345e291375e7d71fb9344f296d97b94117c5fc97c38c9a79f9ff58b47c9729459fd9ad9f012d98197781153168294c75c98798578f67492f7639578b82ec37a8cd5ae9be95497f9225bf96d1b25249934e892d37f3484e594f3b0ae67508d999d9dc98b9fe5ff99f4c593c6c987a440a8c6078e245e81390452e9b26138289043cd921af331d961a6e45b8b697b9c1af2a2b45a482a3d8e264481c8ad453a8e91d8ab1876db86e8cd6a360d8206596fe94c833a218999094148ac9504ed8d61184cf95d8e3a7d89765f924add60e845a7e857740ab75a48b3415a661309316451017cb90b78b980a4f8756a271b9209c8260696a8f8fc913a4095096b48d7ca521a743727c196e9ec931a929121ad6f7a95a6264d923913974ffaec7e1a6548d564a7f678a1e6d1966a38a92a8c368a9c92966296d9d8a0d9596b3ad68f01d81052167ef6849de77aaf1aa57621ad66f98a6a5a20aeaa60a6a1f5a14916aa34a23f44de1377667f0a25976791428a594db6f6a4f3c0a2c681a81a0aaa981caf58434d897f6977e2a57972a7e989ad3a9d6a27a77ac3d16179ea8089b353c8816f799da5057da2c89da3aa867e36581dd7979c69fc84fae6536a11a4835488913370958fa8a9509be7c77e711fa06a5a954a85a673fd400bada7989ea9f85f80c98373aadea4575511faa173c9f0b3b9109b6665834169ac3ad0b9c4ec77d1976b2731b8ea51b45171be8a80949a5e6c6a22bc9442bd01d0095ff6cea92b20b971c2b1aa186f2b42a9f9dfac4a1244f9103000337129bf9e99c4aa2b05140b9ba60b15725b8039944cad7ae4562355b31a8d95ca93b96730bfe741a65991af590ca2d6567b817ea28ae0bec831877a79a12b611d4bd774d5ed793a9b85da97bdd46c98ea32baeaca1f6bc3a17b51137b1079d1f1713b13b618c91618399caaed405afd9f8bb4bb0beea9760faed1c65a9bb65052b6535a02a402cd1a95401da9d7b33b87a7ba92a98b48ba3b2f83d52e1385be190092a5273a1574c7bb6be7b48a74118bada38b41158bd312a63d50f38513cac0bea5c8bd37ed9c0b20486829b83bb6b1cb027fabc511bb99b12b9cb6814686c925a8b350acbffbaf9efa4993eb69bd385813cb1bb271385ffa3f714b581c5929aed41690dbd5b2dbdab681ab6afbc85bfb9b6de5c0b7770c137531928b85bf7b4ebd7182b7fbf5babba542f60b8cc47878b9d336c8353cf83d9a7b3e932a0b30893db2281ab4474e3f0c93ab336f6f9ba2aca7806b79a771e9edaabae51e1c552b99ed7c24f0c19b6035bb119883e6902586a366fa9e3c57a4a413c30193c19722cd272c9327b1502b8cb519eb471cce99c9d2c2e6d8944c064de798b32c43bcc4d4c086c3cd29f2b45ca7bd1c8fb52995c65b383b5c1aa52ccc90eb60b7d59aa9885fa5396ebe5794972c00063c05b669323a5b119f2306c71afba56b2f4cb6c0a36b67c275f7359c23e112086ca7cbb1521c11941c05ca2c37937c89cc8a75c987339e33f8c42c15539c99aab49f47897c89890c43acbdbb86fd3a11f16cb875ad4a9e86bb21c2881d162c49b0abb41f699bcc8bf97b8bff165ad7c1ccbd19bc7eb8b164c79a9b9a59acc0fb04ca6ae410260f8c09c31ecc1d193c7bc8b1adb9dbe91dbcd4c8aa827f8194b329e4787c0c1f47adcbdce5c496fdc7ece1936cad49092295dc937fecbdbd37828278bdce6c54bf65449d39c8baa6a11839b095fcf31cc9fb1468aec3a110c92a51a449e0d68169821d5013ccb8c19ca25659d7cd4a6799db5ac00dbac8f1d73e1d514feb9b122d8bc7d445a97110100b3
;; </COVER>

