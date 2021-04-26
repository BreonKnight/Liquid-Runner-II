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

(var total-possible-score 0)
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
(global es enemies)

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
  (set pipe.from (group pipe.from-x pipe.from-y flags.water []))
  (let [rows (group-by pipe.from #(. $ 2))
        [top-y] (doto (keys rows) (table.sort))
        top-tile (mget (table.unpack (. rows top-y 1)))
        level (tile-level top-tile)]
    (when (<= 1 level)
      (each [_ [tx ty] (ipairs (. rows top-y))]
        (change-level tx ty -1))
      (drain-to pipe))
    (when (<= level 1)
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
(fn enemy-move [dx dy pursue ?retry i]
  (fn [e]
    (let [{: x : y} e]
      (set [e.x e.y] [(+ e.x dx) (+ e.y dy)])
      (when (and (= (/ e.x 8) (// e.x 8)) (= (/ e.y 8) (// e.y 8)))
        (set e.update pursue))
      (when (inside? e flags.wall)
        (set [e.x e.y] [x y])
        (pursue e i (not ?retry)))
      (when (and (not (stand-on? e flags.wall))
                 (not (stand-on? e flags.ladder))
                 (not (inside? e flags.ladder)))
        ;; gravity
        (set e.y (+ e.y 1))))))

(fn enemy-pursue [e i ?retry]
  (let [dx (- player.x e.x)
        dy (- player.y e.y)
        c1 (enemy-pursue-first-choice e dx dy)
        c2 (enemy-pursue-second-choice e dx dy c1)]
    (match (if ?retry c2 c1)
      :left (set e.update (enemy-move -1 0 enemy-pursue ?retry i))
      :right (set e.update (enemy-move 1 0 enemy-pursue ?retry i))
      :up (set e.update (enemy-move 0 -1 enemy-pursue ?retry i))
      :down (set e.update (enemy-move 0 1 enemy-pursue ?retry i)))))

(fn reset []
  (sfx -1)
  (sync 4 1 false)
  (into player checkpoint-player)
  (each [k (pairs active-pipes)]
    (tset active-pipes k nil))
  (each [_ [px py flag] (pairs checkpoint-pipes)]
    (activate-pipe px py flag))
  (each [i [ex ey] (ipairs checkpoint-enemies)]
    (let [e (. enemies i)]
      (set (e.x e.y) (values (// ex 1) (// ey 1)))
      (when (= e.spr 482) (set e.update enemy-pursue))))
  (set player.reset -100)
  (set player.msg nil))

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
    (sfx 61 "A-4" 90 1)
    (set player.ded 0)
    (set _G.TIC ded)))

;;; checkpoints

(fn count-reset []
  (set player.reset (+ player.reset 1))
  (when (= 60 player.reset)
    (reset)))

(fn set-checkpoint [x y skip-flag?]
  (when (not skip-flag?)
    (set player.msg "Checkpoint!")
    (set player.msg-count 90)
    (mset (// x 8) (// y 8) 227)
    (sfx 60 "C#4" 40 1))
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
      (or (= 264 s) (= 265 s)) (if (= dir -1) 288 256)
      (+ s dir)))

(var t 0)

(fn go [dir]
  (when (= (math.fmod t 5) 0)
    (set player.spr (next-spr player.spr dir)))
  (set player.x (+ player.x dir)))

(fn go-v [dir]
  (when (and (inside? player flags.ladder) (= 0 (math.fmod t 10)))
    (set player.spr (if (= player.spr 264)
                        265
                        264)))
  (set player.y (+ player.y dir)))

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
      (go-v -1))
    (when (and (btn 1) (down-ok? player))
      (go-v 1))
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
    (when (btnp 5)
      (set (player.x player.y)
           (values (* player.cheat-x 8) (* player.cheat-y 8))))
    ;; (when (btn 7)
    ;;   (set (player.x player.y)
    ;;        (values (* player.cheat2-x 8) (* player.cheat2-y 8))))
    )
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
(local bomb-notes {336 "D-3" 337 "D-6"})

(fn trigger-bomb [b]
  (let [affected (group (// b.x 8) (// b.y 8)
                        (. bomb-flags b.sprite) [])]
    (sfx 57 (. bomb-notes b.sprite) 30 2)
    (each [_ [x y] (pairs affected)]
      (if (= 336 b.sprite)
          (melt x y)
          (freeze x y)))))

(local dialogs
       {"6x131" ["\nWhat are you doing here?"
                 "Oh, you're searching for the alexis
self-destruct code? Awesome.
You've come to the right place."
                 "These flash drives contain anti-labor
propaganda. I'm replacing their data
with something a little more ... spicy."
                 "You can help out the workers' cause
by doing the same if you see any more
of them deeper in the warehouse."]
        "51x92" ["Nice going.\nYou're making good progress
but there's still a ways to go."
                  "There's a password you can use
to jump to this point.
Hold down A and press X next time."]})

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
        "74x130" (no-water "Son of a melonh*cker!" 74 132)
        "26x107" "Let me go drain that water to the right."
        "83x128" "That fella up there looks like trouble."
        "91x86" "This is it; the final checkpoint."
        "99x106" "Whew; that thing can't swim."})

(fn show-msg [cx cy]
  (mset cx cy 0)
  (let [msg (. msgs (xykey cx cy))
        (msg ?duration) (if (= :function (type msg))
                            (msg)
                            msg)]
    (set player.msg-count (or ?duration 220))
    (set player.msg msg)))

(var win-t -20)

(fn win []
  (cls)
  (set win-t (+ win-t 1))
  (when (btnp 5)
    (reset)
    (set _G.TIC _G.play))
  (spr 400 16 16 -1 2 0 0 4 4)
  (if (= player.score 10000)
      (do (spr 368 100 10 0 1 0 0 2 2)
          (print "Wow, perfect score!" 120 16 12))
      (do (print (.. player.score " points") 150 10 8)
          (print (.. "out of " total-possible-score) 158 20 8)))
  (print "YOU WIN" 75 92 14 false 3)
  (print "alexis self-destruct:" 100 38 3 false 1 true)
  (print "ACTIVATED"
         (+ 111 (math.random 3))
         (+ 52 (math.random 3)) 2 true 2)
  (for [i 1 (// win-t 10)]
    (circ (+ 32 (math.random 32)) (+ 32 (math.random 32))
          (math.min (// win-t 10) 28) 0))
  (print "By Phil Hagelberg, Zach Hagelberg, and Breon Knight"
         (- 260 (math.fmod win-t 550)) 120 12))

(local pickups {228 100 244 500})
(local pickup-replace {100 213 500 0})
(local pickup-notes {100 "B-5" 500 "B-4"})

(fn pickup [points x y]
  (mset (// x 8) (// y 8) (. pickup-replace points))
  (sfx 62 (. pickup-notes points) 17 3)
  (set player.score (+ player.score points))
  (when (= 10000 player.score)
    (mset 127 65 199)
    (mset 128 65 183)))

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
      points (pickup points x y))
    (match (. pickups foot-tile)
      points (pickup points x (+ y player.h -1)))))

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
  (each [i e (pairs enemies)]
    (e.update e i)
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
    (set player.msg-count (- (or player.msg-count 220) 1))
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
    (when (= 238 (mget x y))
      (mset x y 0)
      (set (player.cheat2-x player.cheat2-y) (values x y)))
    (match (. pickups (mget x y))
      points (set total-possible-score (+ total-possible-score points)))
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
(set-checkpoint player.x player.y true)

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
;; 144:e56666fe5666666f66666666666666666666666666666666ffffffffeeeedeee
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
;; 182:d56666fdddddddddd56666fdd56666fdd56666fdddddddddd56666fdd56666fd
;; 183:000000dd0000000d0000400d4004c40dc44ccc0e00c0000e0000000e000000ee
;; 192:056666f05666666f66666666666666666666666666666666ffffffff00000000
;; 193:000000005555555566666666666666666666666666666666f666666f0f6666f0
;; 194:056666f005666665056666660566666605666666056666660566666f056666f0
;; 195:056666f0566666f0666666f0666666f0666666f0666666f0f66666f0056666f0
;; 196:056666f05555555566666666666666666666666666666666ffffffff056666f0
;; 197:030902000eeeeeee0e4e00000eeeeeee0e4eeeee0eeeeeee000d0000000d0000
;; 198:00900000eeeeee00eefffe00eeeefe002e6eee002e6eee002060000020600000
;; 199:dd000000d0000000d0040000d04c4004e0ccc44ce0000c00e0000000ee000000
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
;; 214:20600000206000002060000020060000020066660020e0e0000222220000e0e0
;; 215:000deeee00deeeee0ddddddd0deeeeee6deddddd0dedeeee2deeeeee0deeeeee
;; 216:0309020003090200030902000309022203009200030099990309020003090200
;; 217:0000000000000000000000002222220200000020999000990099990000090000
;; 218:0000000000000000000000002000000002222000909002000999002000009022
;; 224:eeeedeeeeeeedeee66ddeddde6eeeeeee6eeeeeeedeeeeeeded66666eeee6eee
;; 225:eeee6eeeeeee6eee66ddeddde6eeeeeee6eeeeeeedeeeeeeded66666eeee6eee
;; 226:0000000000222000002d2000002d0000000d0000000d0000000d0000000d0000
;; 227:0000000000022000000d2200000d4220000d2442000d0224000d0002000d0000
;; 228:00ddd00006ddd600066466000664660006644600066666000066600000000000
;; 229:00000ddd0000deee0000deff0000def60000deff0000def60000deff0000deff
;; 230:ddddddd0eeeeeed0fffffed066fffed0fffffed06ffffed0ff66fed0fffffed0
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
;; 254:0ccccc00cc222cc0cccc2cc0ccc2ccc0ccc2ccc00ccccc000000c000000c0000
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
;; 008:00bbbb0efbbbbbb44bbbbbb44bbbbbb440bbbb04400440400411140000111000
;; 009:e0bbbb004bbbbbbf4bbbbbb44bbbbbb440bbbb04040440040411144000111000
;; 012:00bbbb0efbbbbbb44bbbbbb44bbbbbb440bbbb04400440400411140000111000
;; 013:e0bbbb004bbbbbbf4bbbbbb44bbbbbb440bbbb04040440040411144000111000
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
;; 024:0011100000111000001110000099900000999000009090000090ff000ff00000
;; 025:0011100000111000001110000099900000999000009090000ff090000000ff00
;; 028:0011100000111000001110000099900000999000009090000090ff000ff00000
;; 029:0011100000111000001110000099900000999000009090000ff090000000ff00
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
;; 145:00000000000000000000000000000000000000000000000000000eee0eeeeeed
;; 146:000000000000000000000000000000000000000000000000eeeeee00ddddddee
;; 147:00000000000000000000000000000000000000000000000000000000ee000000
;; 160:000000ee0000eeed000eeddb00eeddbb00eddbbd00eddbdd00eddbbd00edddbb
;; 161:eedddddbdddbbbbdbbbbddddddddddddddddddddcccddddddddddddddddddddd
;; 162:bbbbddddddddbbbbdddddddddddddcddddddcccdddddddddddddddbbddddbbbd
;; 163:dee00000dddee000bdddee00bdddde00bdddee00bddde000ddffef00dffdef00
;; 176:000fdddb00fdffdd00fdddff00fddddd00fdddd200fddddd00fddddd00fddddd
;; 177:bbdddddddbbbbbbbffddddddddffffff2dddddddd2ddddddddddddddddddd2d2
;; 178:dbbbbddfbbdddfffddffffddffddddddddddd22ddddd2dddddddddddd2dddddd
;; 179:ffddef00ddddef00ddddef00ddddef00ddddef00dddeff00dddef000dddef000
;; 192:00fddddd00fedddd000ffffe000000ff00000000000000000000000000000000
;; 193:ddddd2d2ddddd2d2eeedddddffffffff00000000000000000000000000000000
;; 194:d2ddddddd2dddeeedddddfffffffff0000000000000000000000000000000000
;; 195:eeeff000ffff0000f00000000000000000000000000000000000000000000000
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
;; 053:000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e1e1e1e1e1e1e1e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 054:000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001900000000000019000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 055:000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c4b4b4b4b4b4b3c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 056:000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c4b4b4b4b4b4b3c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 057:000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c4b4b4b4b4b4b3c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 058:000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c4b4b4b4b4b4b3c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 059:000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c4b4b4b4b4b4b3c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 060:000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c4b4b4b4b4b4b3c001b4b3b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 061:00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000290e0e0e0e0e0e29002c4b3c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 062:0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000108c00000000000029d8d8d8d888d829002c4b3c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 063:0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200d1d0d1d0d1d0d29d888d8d8d89829802c4b4c3b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 064:00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c4a4a4a4a4a4a4a094a3a2d0e1f29291b4c4b4c2b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 065:0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000004d00000a3a1f4d2020302c4b3c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 066:000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020bc00bc00bc008d9dadbd0b4b4b4c2b002c4b3c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 067:0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000005c6c5e6e0000402c4b3b2c4b3c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 068:00000000000000000000000000000000000000000000000000001f1f1f1f1f1f1f1f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000002f6d7d6f000040201b2b2c4b3c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 069:000000000000000000000000000000000000000000000000004d04545454045404041e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000002d3d0f000f0000000000000000000000000000000000000000000000000000000000000000000000200000000000001f1f1f3d400040200b3b2c1c2b00000000000000000000000000000000001b3b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 070:000000000000000000000000000000000000000000000000001e08585808580808581e1f0000000000000000000000000000000000000000000000000000000000000000000000000000000000002d3d00002d3d00000000000000000000000000000000000000000000000000000000000000000000002c4b4b4b4b4b4b1c4b4b4b4b3b400b4b0c0c0c4b4b4b4b4b4b4b4b4b4b4b4b4b4b4b4b4b4b3c2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 071:000000000000000000000000000000000000000000001f000e585858085858585858580e1f4d000000000000000000000000000000000000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e0e0e0e0e3d00000000000000000000000000000000000000000000000000000000300000000000003000bc00003040000000000000000000000000000000000000000000001b0c3c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 072:0000000000000000000000000000000000001e1e1f1f1f0e000e0e0e0e0e0e4d0e0e0e000e1f1f1f1f3d1e1e000000000000000000000000000000000000000000000000000000000000000000000e0000000000000f3d0e0000003d0000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000b4b2b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 073:00000000000000000000000000000000001e00000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000000000000000e00000000000000000e0000003d00000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 074:00000000000000000000000000000000001f000000000000ff0000000000000000008c0000000000000000001f0000004e00000000000000000000000000000000000000000000000000000000000e00000000000000000e400e001e00000000000000000000000000000000000000000000000000000000000000000000000000000000401000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 075:00000000000000000000000000000000001f0000000d0000000000000000000000000000000000001d0000001e1e1e004e00000000000000000000000000000000000000000000000000000000000e400ec888888888880e400e001e00000000000000000000000000000000000000000000000000000000000000000000000000000000403000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 076:0000000000000000000000000000000000003d1f1f0e1f1e400e0e0e0e0e0e3d0e0e0e401e1f1f1f1f1f1f0f0000001e404e4e00000000000000001e1e00000000000000000000000000000000000e400e0e0e0e190e0e0e402d001e00000000000000000000000000000000000000000000000000000000000000000000000000000000400000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 077:00000000000000000000000000000000000000000000001e400e00000000000000000e401e4d001f3d1f000f0000000f00000000000000000000002e1e0000000000000000000f0f0f0f0f0f0f0f0f400e00000030000000400e001e000000000000000000000000000000000000001b4b4b4b4b5b4b4b3b40000000000000000000000040000000400000000000001b4b4b3b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 078:00000000000000000000000000000000000000000000001e400e00000000000000000e401e001f001f00000f0000001e0f1e0f0858480f400000002f1e00000000000000003d085858580858580f0f404000000000000000400e001e00000000000000000000000000000000000000200000000040000020400000000000000000000000400000004000000000001b0c3b1b2b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 079:00000000000000000000000000000000000000000000001e402e000000000000001d0e401e0e0e0e0e0e0e0e400e400e0e0e0e0e0e0e0e0e4040400e0e0e0e0e0e0e1f1f1f1f585858585808580f0f404000000000000000400f001e0000000000000000000000000000000000000020000000404f0000204000000000000000000000004010000040000000001b3c1b2b0b3b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 080:00000000000000000000000000000000000000000000001e402f000000000000401e40401e000e0000000000400f40404040404040404040404040404040404040404040401f085858085858580f2d404000000000000000400f002d0000000010400000000000000000401040000020000000000000003040000000000000000000000040200000400000001b3c20201b3b20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 081:000000000000000000000000000000000000000000000f1e1e3d00000e48480e401e40400e1f000000000000400f00000000000000000000000000000000ac0000004f00001f580858585858080f0f404000000000000000000f001e000000002c4b4b4b4b4b4b4b4b4b4b3c4000006b0000000040100000400000104000000000000000402000004000001b3c20200b2b2c2b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 082:000000000000000000000000000000000000000000000f1a3a0e00004d48480e404d40400e000000001d0000400f40404040404040404040404040404040404040404040403d085858585808580f0f40401e000000000000002d001e000000003000000000000000000000204000006b00000000402000004000000b1c5b1c4b4b4b4b4b4b0c3b0040001b3c20202c3b1b2b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 083:000000000000000000000000000000000000000000000f0a2a0e790e0e190e0e401e401e0e0e0e0e0e0e0e0e0e0e40404040404040404040404040404040404040404040401f2d5858585858582d0f40400e3d0e0e3d1e0e0e0e001e0000000000000000000000000000002c4b4b4b4c4b4b3b00402c4b4b3b400000204020000000000000002000401b3c200b4c2b2c2b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 084:00000000000000001e1e1e1e1e1e1e3d1e1e1f1e1e1f1e1e0e1e600000200000401e401e0000000e0e3d0000000e00000000000000000000000000000000ac00000e0e0e0e0e0e0e0e3d1e58580f0f404000000000000000000e001e0000000000000000000000404000006b000000200000209c4020000020400000204020000000000000000b4b5b3c3020000b4b2b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 085:000000000000000f0000000000000000000000000000001e0000602d00300000401e401e002e000000000000000e404040404040404040404040404040404040400e00000000002d4040401e2d1e0f404000000000000000000e001e000000004e000000000000404e00006b0000002000002000402000002040000030402000000000000000000040204e2c3b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 086:0000000000003d40000000000000000000000000000000000000602d00000e401e1e401e002f000000000000000e404040404040404040404040404040404040400e00000000001e4000401e0f1e562d4000000000000000000e2eff0000000000000000000000400f001b2b0000000b4b4b4c4b4b2b00000b5a3b00004020000000000000000010400b5b2b20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 087:00000000001e1e1e1e401e1e1e1e1e4d1e1e1e1e1e00001f401e6a0000000e401e00401e400e40000000000e400e0e0e400e000000000000000000000000ac00000e1e400e00003d400e401e5858583d0e0e480808080e401d0e2f000000404d3d1e2d00000000002d002000000000000000200000000000004020000040200000000000000000204000400020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 088:000000001e0000000040000000000000000000001e000000401f1e1e1e1f1e401f004000400e00000000000e400e402e400e4040404040404040404040404040400e3d400e000000000e401e5858583d0e1e0e0e190e1e400e0e3d4d3d1f1f1f00001f1b4b4b4b4b4a4b2b00004000000000200000000000004020000040200000000000000000200000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 089:000000001e0000000040000000000000000000001e000e00400000000e1e1e401e004000400e790e0e0e190e400e402f400e4040404040404040404040404040400e1e400e000000000e401e5858584d0e1e1e1e391e004000000e0e0e00000000003d20000000003d00000000400000000020000000401b4b4a3c0000402000000000000000000b4b4b4b4b2b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 090:000000000e000000000000000000000e0e0e40003d000f0040000000000000401e2e40004000600000002000400e400e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e400e1e400e0e790e0e0e401e5858583d0000000000404040000000000e005e6e00000f2000001a3a2d00001b4b5b4b1c5b4b2b00000040291e1e29000040200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 091:000000000e0000000000000000000e4e4e0e40001e000f1d40000000000000401e2f40004000600000000b4b5b3b400e00000000000000000000000000000000400e4d4000006000000e401e1818180f0000000000000040000000000e005f6f00001f2000000a2a0f3d3d290040002000000000000040291e1e29000040200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 092:0000000000790e0e0e3d0e0e0e190e00000e40001e00001e00401e4000001e1e1e1f1e1e1ec8e888880e00004030401e00007eef0000fe000000000000002e004000004000006000000e401e2929290f000000000000400e0e1e1e400e1f4d1f1f400f20003d3d0e0e0e3d290040002000000000000040294d1e0b4b4b4b2b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 093:000000000060001e3d00000000300e40400e40001e00001e00401e0000001e000000002d0e886a88880e00000000001e0d007f00000000000000000000002f00400f3d4000006000000e401e3838381f400e000000000e402e0000400e05550555453d201e4d000000000e290040002000000000000040291e1e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 094:000000000060001f0000000000000e40404d40001e0f001e00401e1e791e1e001000002d000e0e0e0e0e00000000001e0e0e0e3d0e0e0e0e0808081f0e0e0e3d0e0e0e401e88e888883d401e5858583d400e1e1e2d0e0e402f0000400e58585858484d0b4a3a000000001e2c4b5b4b3c000000000000406b001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 095:0000000000602d000000000040000e40400e40000d0f001e0040000060002d0020001b4a4b3a0000000f1e1e1e1e1e004d002d404f1e580e5808580e004f404040401e401f88e888881e401e5858580f4000000000000e400e0e0e0e0e0e0e0e3d0e0e0e0e391e4000000e29004f0020000000000000406b001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 096:0000000000600000000000400e000000000000003d2d001e0d40000060000000200020000029001b4b4b4a4a4a4b3b0000002d40001e581f585858581e00000000401e401e886a88881e401e0e1e3d3d4000000000000e400e0000000000000000000000000000001e400e0b4b4b4b0c4b4b4b4b5a4b5b2b401e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 097:0000000000600000000000400e000000000000000f1f002e401ec888e81e00000b4b2b00002900200000003d00003000000000402d1e1f0e08585858081e000000001e401f1e1e1e1e1e401e0f1f1f0f4000000000002d0000000000000000000ed181d1d181d1811e400e00000000000000000040004000401e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 098:0000000000600e0e0e400e0e1f0e0e1f3d0f0f0f0f00002f401ed8886a1e0e000000001b4b4c4b4c4b4b3b3d0000000000000040003d580f585858580808580808581e40001f000000000000001f1f1e4040000000000e000000000000000e400e88d88888d8d8881e400e00000000000000000040004000401e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 099:000000000060000e00400e002e00001e0f0f1f0f0f0f0f0f0f0f1f1e1e002d0f2d000020002000200000291e0000000000000040001f580f58083d085858580858082d00001f00000000002e000000000040bc0000000e000000000000000e400e0e0e190e0e3d0e1e400e1e000000000000000040004000401e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 100:000000000060004d00401e002f001e1e1e000000000000000000000000002d000000000b4b2b000b3b00290e0000000000000000003d580f083d3d0f080808580858580808581f000000002f000000000040400000000e0e0e0e0e0e0e790e400e000030404000000040000e00000000000000004000401e401e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 101:000000000060001e000000001e401e001e002e0000000000000000000000000000000000000000002000200f404040404040401e401f1f0e2d1e003d1f1f0e0e1e5858585858581f1f0e0e0e000000000040401d0000001e085808080e600000000000000000000000402e3d009c0000000000004000401e401e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 102:000000000060001e000000004d401e001e002f0000000000000000000000000000000040000000000b4b2b1f585818081808081e401f1f1f00000000000000004d58585858581e4040bc4f1e00000000ff4040400000001e080858080e6000000000000000001e4040402f0e00000000000000004000001f401e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 103:000000000060001e191e791e1e403d000e400ec88888c80e1f1f40000000000000000e40000000000000001f1a4a2a1e391e1e1e401f3d1f00000000000000001e581e1e1e1e1e404000001e00000000004040400000001e085858080e6a00000000000000000e4040400e0e4d0e0e0e1f1f1f1f1f1f1f1f401e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 104:00000000006000002000604040401e000e403d190e3d0e0000001f1f1f1f1f1f1f1f1f400000002d0d1e1d1f3000000000000000402d581f5e6e5e6e5e6e5e6e004d0000000000404000001e1e88d8c80e40404000000d0e0e0e0e0e0e0e0e0e3d0e0e0e4d0e0e4040400000000000003d3d1f2d0f1f0e2d401f0f1f4d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 105:00000000006000002000604000001e000e400e390e0e0000000000000000000000001f40004f00003d1e3d1f0000000000000000401f581f5f6f5f6f5f6f5f6f00001e004e000040400000000e8888d81e4000001e1e1e1e00001b4b3b00001e1e1e1e0e0e00004040400000000000000000001f00000e4e001f00001f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 106:0000000000600000200060400e4d000000400000000000001d0000000000000000001e4000000000000000000000003d0000400e401f4d1f1e1f4d1e3d1f1f1f00001f0000000040400000000e0e190e1e4000000f0e4d1e070e0b4b2b0e071e1e1e00ff0000004040400000000000000000001f00004d03531f00001f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 107:00000000006000002000604000000000004000000000000040ff00000000000000001e4000000000000000000000000e1808080e404d1f1f5e6e5e6e5e6e5e6e0000000f3d3d0e40400000000000291e004000000f0e0e0e0e4d0e0e0e0e0e0e0e1e000000401e0e4d0e0e4d0e0e1e400000001f1f1f0e2d1f3d1f003d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 108:000000000060000020006040000000000040000000000000400000000000000000001e4000000000000000000000001e291e1e0e401f0e1f5f6f5f6f5f6f5f6f00000000000e2e40400000000000291e004000000f0000000000000000000000001e1e402d3d4d0000000000000e0e400000003d00000e00000f00000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 109:000000000e600000300e6848081e08481e400e000000400e1e1e400e4848480f40001e4000000000000000000000000030000040401f0d1f2d2d3d2d2d4d2d1e00000000000e2f4040000000000d3940404000000f00000000000000000000000000004000000000000000004f000e400000001f00000e00001f00002d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 110:000000000e6a0000000e6a58081e58581e400e0e0e0e0f0e1e1e400e0e0e190f40001e000000000000000000000e400000000040401f1f1f00000000000000000000000000000e401e1e1e1e1e1e0040404000000f000000000000000000004f000000400000004f00000000001e0e400000001f1f2d0e2d001f1f1f1f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 111:0000001f0e0e0e0e4d0e1f1f1e1e1e1e1e401e1e3d1e1e1e1e1e400e0f0f290f40401e000000000000000000000e000000000e40402e002d000000000000000000000000000000400000000000000040404000000f000000000000404040401f065606065606061f401e1e1e1e1e4d400000004d00000e00000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 112:00001f1f0000000000000000000000000040000000000000001e400e0000300000401e1e3d1e1e1e1e1e1e1e1e1e000000000f40402f001e00000000000000000000000000000040000000000000004040401e1e0f000000000000000000000f585858585808581f4000000000000e400000001f00004d00003d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 113:001f1f000000000000000000000000000040000000000000001e400e0000000000401e000000001e3d000000001e1e3d1e1e1e1e1e1e403d0000000000000000000000000000002d000000000000000f404040400e00000000403d1e3d3d1e0f580858585858581e4000000000004d400000002d00000e0f2d0f2d2d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 114:1f1f000000000000000000000000000d0040000d00000000001e400e00000000ff401e000000000e0e000000000000000000001e0000401e0000000000000000000000000000002d000000000000000f404040400e000000004000000000002d585858085808582d4000000000000e400000000000000e00003d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 115:1f000000008c0000000000000000000e0d400d0e00000000001e400e0000000000401e000000000000000000000000000000001e0000403d0000000000000000002d4000000000400f0f191e3d3d0f0f404040400e000000004000000000001e2d0f2d1e1f0f0f0f40000000000d0e400000000000000e00003d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 116:1f0000000000000000000000000000003d0e0e0000000000001e400e400f0000400f1e0e400e888888c80e40000000000000001e400f1e1e0f0f0f0f2d0f0f000f0e1848080e4040404030001a3a0000404040400e00000000400000000000000000000000000000403d0e0e0e1e1e1e4000000000002d1f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 117:000000000000000000000000000000000000000000000000001e400e000e0e0e0e0e0e0e400ed8d8d8d80e40000000000000001e400f000000000000000000001e1e291e2d1f4d40404000000a2a0000404040400e0000000040000000400000000000000000000040000000003d4f1e485858481e400e00001f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 118:00000000000000000000000000ff00000000000000000000001e400e000000000000000e400e3d0e0e0e0e40000000000000001e400f000000000000000000001e0030000e40001e0e2d000000000000404040400e3d1f1e1e1e1e3d1e400000000000000000000040000000003d401e1e1e191e1e400e00001f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 119:00000000ff00000000000000000000000000000000000000000e400e000000000000000e4000000000000040000000000000000e4000000000000000000000008c0000000e0040404040404040404040404040400e0000000000001e00400000000000000000000040000000003d401e2d2d291e2d402d2d3d1f3d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 120:0e00000000000000000000400e0e0e06560656460e0e0e40400e400e2e00ff00000000004000000000000040000000000000000e400000000000000000000000000000004d400040000000000000400e0e0e0e0e0e0000000000000000400000001e3d3d3d403d3d3d3d3d40403d401e1e1e393d1e400e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 121:0e0e0e0e0e0e0000000000400e003d08085858480e000000400e400e2f0d00401fc38383c30e4000001d00400e3dc585c50e400e400e00000000000000000000000000000e00400e0000000000000e0000000000000000000000000000400000001e00000040000000000000400040000000002d1e400e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 122:000e0e0e4d0e0e0e0e0e0e0e0e000e08580808480e000000400e400e1f0e0e3d1fd8d8d8d80e0e0e0e4d0e0e0e0ed898d80e400e400e0e0e1e00004f000e2d0e1e4040404d40000e0000000000004d000000000000000000000000000040000000001e000040000000001e00400040000000000000400e2d3d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 123:001e58581f581f5858580e0000000e48481808480e000000400e4000000000001e1e1e0e0e0e000000000000000e0e290e0e400e400e0e1e00004f000e1e4d40404040400e00400e0e0e0e190e0e0e0000000000009c0000000000000040000000001e000040000000001e00400040000000000000000e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 124:00002d3d4d0f1f2d3d4d0e0000000e1a4a2a0e0e0e000000400e40002e00000000000000000e000000000000000000300000400e400e00000000000e1e404040404040400e00004040401a2a0000000000000e4f000000000000000000400000000000000040000000002d0e400e0e0e401e400000002d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 125:000e0d0000000000001d3d000000002000000000ff000000400e40002f00000000000000003d000000000000000000000000400e400000000000008c00000000000000000e4040000000290e0000000000001e1e1e1e1e1e1e1e1e1e1e404040404040000040000000001e0040000000401e0e2d0e0e2d3d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 126:000e0e0000000000000e0e00000000200000000000000000404d0e1e1e4000000000400e400e00000000400e400000000000400e400000000000000000000000000000000e00000e4d0e390e000000000000000000000000000000000040000000001e1e0e0e0e40004f1e0000000000401e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 127:001f1f190f190f190f0f0e0000000030000000400e4d0e0e0e0e00000eff00000000000f400e00000000400e00000000400e0e0e400e40000000000000000000000000002d0e0e0e0000000e00002e000000000000000000000000000040000000001e0000000040003d1e1e1e1e1e1e1e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 128:0e1f003000300030001e4d00000e400000400e0e0e000000400000000e0808080818080f404d004e0000400e00000000400e0000400e0e1e0e0e1e000e0e2d1e0f4040402d0000000000000e00002f00000000ff00000000000000000040000000001e000000004000001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 129:1e4d000000000000003d0000000e000000400e0000000000000000000e3d0e0e1e290f0f400e00000000404d0e0e0e4d0e0e0000400e0e2d0e1e0000000e1e40404040400e400000400e000000400e1e1e000000000000000000000000400000000000000000004000001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 130:1f1f00000000000000000000003d000000400e0000400e0e000e002e00000000ff300000400e0e0e0e0040000000000000000e00400e00000000000000000000000000000e400000000eff0000004d00001e2d1e1e1e1e40000000401f1f1f1f1f40000000000040001e1e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 131:1e1f004e007eef0000000000000e000000000e000040000e400e002f0000000000000000400e00000e0040000000000000000e004000008c0000000000000000000000000e400000400e000000000e000000000000001f1f1f2d1f1f1f0000001f2d1e1e1e2d1e1e1e1e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 132:1f1f0040007f00000000000000000e0e0e0e4d0e0e400e0e400e0e0e0e0e400040000000ff004f000e004000000000403d2eff00400000000000000000000000000000000e400000000e000000000e00000000000000000000000000000000001f1f1f1f1f1f1f1f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 133:001f1f1f1f1f1f1f1f4d0e400000ff0000000000ff40004f400e0000000e400040000000000040000e004000000000401f2f0000400e40004e004e00000000001e00000000001f3d0e0e0e0e0e0e0e000000000000000000000000000000000000001f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 134:0000000000000000000e0e40000000000000000000400000401e000000000e0e0e1f1e1e1e4d0e0e0e0e0e0e4808580e0e0e4d0e0e0e0000000000000000000f2d00000000001f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 135:000000000000000000000e0e0e0e0e4d0e0e0e0e0e0e0e0e0f000000000000000000000000000000000000000f0f0f000000000000001f1f1f1f4d1f1f1f1f1e1f1f1f2d1f1f1f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; </MAP>

;; <MAP1>
;; 001:00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 067:000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003d5e6e0000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 068:00000000000000000000000000000000000000000000000000001f1f1f1f1f1f1f1f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003d5f6f0000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 069:000000000000000000000000000000000000000000000000004d04545454045404041e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000002d3d0f000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000003d3d3d4000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 070:000000000000000000000000000000000000000000000000001e08585808580808581e1f0000000000000000000000000000000000000000000000000000000000000000000000000000000000002d3d00002d3d0000000000000000000000000000000000000000000000000000000000000000000000000000000000001b4b4b4b4b3b400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 071:000000000000000000000000000000000000000000001f000e585858085858585858580e1f4d000000000000000000000000000000000000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e0e0e0e0e3d0000000000000000000000000000000000000000000000000000000000000000000000300000000030400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 072:0000000000000000000000000000000000001e1e1f1f1f0e000e0e0e0e0e0e4d0e0e0e000e1f1f1f1f3d1e1e000000000000000000000000000000000000000000000000000000000000000000000e0000000000000f3d0e0000003d00000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 073:00000000000000000000000000000000001e00000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000000000000000e00000000000000000e0000003d00000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 074:00000000000000000000000000000000001f00000000000000000000000000000000000000000000000000001f0000005d00000000000000000000000000000000000000000000000000000000000e00000000000000000e400e001e00000000000000000000000000000000000000000000000000000000000000000000000000000000401000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 075:00000000000000000000000000000000001f000d000000000000000000000000000000000000000000001d001e1e1e005d00000000000000000000000000000000000000000000000000000000000e400e4000000000000e400e001e00000000000000000000000000000000000000000000000000000000000000000000000000000000403000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 076:0000000000000000000000000000000000003d1f1f0e1f1e400e0e0e0e0e0e3d0e0e0e401e1f1f1f1f1f1f0f0000001e405d5d0000000000000000000000000000000000000000000000000000000e400e0e0e0e190e0e0e402d001e00000000000000000000000000000000000000000000000000000000000000000000000000000000400000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 077:00000000000000000000000000000000000000000000001e400e00000000000000000e401e4d001f3d1f000f0000000f000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0f400e00000030000000400e001e000000000000000000000000000000000000001b4b4b4b4b5b4b4b3b40000000000000000000000040000000400000000000001b4b4b3b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 078:00000000000000000000000000000000000000000000001e400e00000000000000000e401e001f001f00000f0000001e0f1e0f88d8c80f40000000000000000000000000003d085858580858580f0f404000000000000000400e001e00000000000000000000000000000000000000200000000040000020400000000000000000000000400000004000000000001b0c3b1b2b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 079:00000000000000000000000000000000000000000000001e4000000000000000001d0e401e0e0e0e0e0e0e0e400e400e0e0e0e0e0e0e0e0e4040400e0e0e0e0e0e0e1f1f1f1f585858585808580f0f404000000000000000400f001e0000000000000000000000000000000000000020000000404f0000204000000000000000000000004010000040000000001b3c1b2b0b3b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 080:00000000000000000000000000000000000000000000001e4000000000000000401e40401e000e0000000000400f40404040404040404040404040404040404040404040401f085858085858580f2d404000000000000000400f002d0000000010400000000000000000401040000020000000000000003040000000000000000000000040200000400000001b3c20201b3b20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 081:000000000000000000000000000000000000000000000f1e1e3d88880e40400e401e40400e1f000000000000400f00000000000000000000000000000000000000000000001f580858585858080f0f404000000000000000000f001e000000002c4b4b4b4b4b4b4b4b4b4b3c4000006b0000000040100000400000104000000000000000402000004000001b3c20200b2b2c2b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 082:000000000000000000000000000000000000000000000f1a3a0ed8884d40400e404d40400e000000001d0000400f40404040404040404040404040404040404040404040403d085858585808580f0f40401e085858085858082d001e000000003000000000000000000000204000006b00000000402000004000000b1c5b1c4b4b4b4b4b4b0c3b0040001b3c20202c3b1b2b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 083:000000000000000000000000000000000000000000000f0a2a0e790e0e190e0e401e401e0e0e0e0e0e0e0e0e0e0e40404040404040404040404040404040404040404040401f2d5858585858582d0f40400e0e0e0e0e0e0e0e0e001e0000000000000000000000000000002c4b4b4b4c4b4b3b00402c4b4b3b400000204020000000000000002000401b3c200b4c2b2c2b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 084:00000000000000001e1e1e1e1e1e1e3d1e1e1f1e1e1f1e1e0e1e600000200000401e401e0000000e0e3d0000000e000000000000000000000000000000000000000e0e0e0e0e0e0e0e3d1e58580f0f404000000000000000000e001e0000000000000000000000404000006b00000020000020004020000020400000204020000000000000000b4b5b3c3020000b4b2b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 085:000000000000000f0000000000000000000000000000001e0000602d00300000401e401e003e000000000000000e404040404040404040404040404040404040400e00000000002d4040401e2d1e0f404000000000000000000e001e000000004e000000000000404e00006b0000002000002000402000002040000030402000000000000000000040204e2c3b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 086:0000000000003d40000000000000000000000000000000000000602d00500e401e1e401e002f000000000000000e404040404040404040404040404040404040400e0000000000004000401e0f1e562d4000000000000000000e3e000000000000000000000000400f001b2b0000000b4b4b4c4b4b2b00000b5a3b00004020000000000000000010400b5b2b20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 087:00000000001e1e1e1e401e1e1e1e1e4d1e1e1e1e1e00001f401e6a0050500e401e00401e400e40500050500e400e0e0e400e0000000000000000000000000000000e1e400e025202020e401e5858583d0e0e400000000e401d0e2f000000404d3d1e2d00000000002d002000000000000000200000000000004020000040200000000000000000204000400020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 088:000000001e0000000040000000000000000000001e000000401f1e1e1e1f1e401f004000400e00000050500e400e403e400e4040404040404040404040404040400e3d400e5e5e5e5e0e401e5858583d0e1e0e0e190e1e400e0e3d3d3d1f1f1f00001f1b4b4b4b4b4a4b2b00004000000000200000000000004020000040200000000000000000200000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 089:000000001e0000000040000000000000000000001e000e00400000000e1e1e401e004000400e790e0e0e190e400e402f400e4040404040404040404040404040400e1e400e085808080e401e5858584d0e1e1e1e391e004000000e0e0e00000000003d20000000003d00000000400000000020000000401b4b4a3c0000402000000000000000000b4b4b4b4b2b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 090:000000000e005050505050005000500e0e0e40003d000f0040000000000000401e3e40004000600000002000400e400e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e400e1e400e0e790e0e0e401e5858583d0000000000404040000000000e005e6e00000f20000000002d00001b4b5b4b1c5b4b2b00000040291e1e29000040200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 091:000000000e0858585808085808080e5d5d0e40001e000f1d40000000000000401e2f40004000600000000b4b5b3b400e00000000000000000000000000000000400e4d4000006000000e401e1818180f0000000000000040000000000e005f6f00001f20000000000f3d3d290040002000000000000040291e1e29000040200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 092:0000000000790e0e0e3d0e0e0e190e00000e40001e00001e00401ec888881e1e1e1f1e1e1e406000000e00004030401e00007e00000000000000000000003e004000004000006000000e401e2929290f000000000000400e0e1e1e400e1f1f1f1f400f20003d1f0e0e0e3d290040002000000000000040291e1e0b4b4b4b2b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 093:000000000060001e3d00000000300e40400e40001e00001e00401e8888881e000000002d0e006a00000e08085858581e0d007f00000000000000000000002f00400f3d4000006000000e401e3838381f400e8888d8d80e403e0000400e05550555453d201e4d000000000e290040002000000000000040291e1e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 094:000000000060001f0000000000000e40404d40001e0f001e00401e1e791e1e001000002d000e0e0e0e0e08580858581e0e0e0e3d0e0e0e0e0808081f0e0e0e3d0e0e0e401e006000003d401e5858583d400e1e1e2d0e0e402f0000400e58585858484d0b4a3a000000001e2c4b5b4b3c000000000000406b001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 095:0000000000602d000000000040000e40400e40000d0f001e0040000060002d0020001b4a4b3a0000000f1e1e1e1e1e004d002d40001e580e5808580e0000404040401e401f006000001e401e5858580f4000000000000e400e0e0e0e0e0e0e0e0e0e0e0e0e391e4000000e29004f0020000000000000406b001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 096:0000000000600000000000400e000000000000003d2d001e0d40000060000000200020000029001b4b4b4a4a4a4b3b0000002d40001e581f585858581e00000000401e401e006a00001e401e0e1e3d3d4000000000000e400e0000000000000000000000000000001e400e0b4b4b4b0c4b4b4b4b5a4b5b2b401e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 097:0000000000600000000000400e585858085858080f1f003e401e4000601e00000b4b2b00002900200000003d00003000000000402d1e1f0e08585858081e000000001e401f1e1e1e1e1e401e0f1f1f0f4000000000002d0000000000000000000e500050500050001e400e00000000000000000040004000401e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 098:0000000000600e0e0e400e0e1f0e0e1f3d0f0f0f0f00002f401e50006a1e0e000000001b4b4c4b4c4b4b3b3d0000000000000040003d580f585858580808580808581e40001f000000000000001f1f1e4040000000000e515101515151013d400e005000005050001e400e00000000000000000040004000401e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 099:000000000060000e00400e003e00001e0f0f1f0f0f0f0f0f0f0f1f1e1e002d0f2d000020002000200000291e0000000000000040001f580f58083d085858580858082d00001f00000000003e000000000040000000000e585808085808080e400e0e0e190e0e0e0e1e400e00000000000000000040004000401e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 100:000000000060004d00401e002f001e1e1e000000000000000000000000002d000000000b4b2b000b3b00290e0000000000000000003d580f083d3d0f080808580858580808581f000000002f000000000040400000000e0e0e0e0e0e0e790e400e0000304040000000400e0e00000000000000004000401e401e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 101:000000000060001e500050001e401e001e003e0000000000000000000000000000000000000000002000200f404040404040401e401f1f0e2d1e003d1f1f0e0e1e5858585858581f1f0e0e0e000000000040401d00001e08085808080e600000000000000000000000403e3d00000000000000004000401e401e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 102:000000000060001e500050004d401e001e002f0000000000000000000000000000000040000000000b4b2b1f505010001000001e401f1f1f00000000000000004d58585858581e404000001e000000000040404000004d58080858080e6050005050505000001e4040402f0e00000000000000004000001f401e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 103:000000000060001e191e791e1e403d000e400e400000400e1f1f40000000000000000e40000000000000001f1a4a2a1e391e1e1e401f3d1f00000000000000001e581e1e1e1e1e404000001e000000000040404000001e58085858080e6a00000000505050000e4040400e0e4d0e0e0e1f1f1f1f1f1f1f1f401e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 104:00000000006000002000604040401e000e403d190e3d0e0000001f1f1f1f1f1f1f1f1f400000002d0d1e1d1f3000000000000000402d581f5e6e5e6e5e6e5e6e004d0000000000404000001e1e0050000e404040000d1e0e0e0e0e0e0e0e0e0e0e0e0e0e4d0e0e4040400000000000003d3d1f2d0f1f0e2d401f0f1f4d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 105:00000000006000002000604000001e000e400e390e0e0000000000000000000000001f40000000003d1e3d1f0000000000000000401f581f5f6f5f6f5f6f5f6f00001e005d000040400000000e0000501e4000001e1e1e1e00001b4b3b00001e1e1e1e0e0e00004040400000000000000000001f00000e4e001f00001f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 106:0000000000600000200060400e4d000000400000000000001d0000000000000000001e4000000000000000000000003d0000400e401f4d1f1e1f4d1e3d1f1f1f00001f0000000040400000000e0e190e1e4000000f0e4d1e070e0b4b2b0e071e1e1e00000000004040400000000000000000001f00004d03531f00001f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 107:000000000060000020006040000000000040000000000000400000000000000000001e4000000000000000000000000e1000000e404d1f1f5e6e5e6e5e6e5e6e0000000f3d3d0e40400000000000291e004000000f0e0e0e0e4d0e0e0e0e0e0e0e1e000000401e0e4d0e0e4d0e0e1e400000001f1f1f0e2d1f0f1f003d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 108:000000000060000020006040000000000040000000000000400000000000000000001e4000000000000000000000001e291e1e0e401f0e1f5f6f5f6f5f6f5f6f00000000000e3e40400000000000291e004000000f0000000000000000000000001e1e402d3d4d0000000000000e0e400000003d00000e00000f00000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 109:000000000e605000300e6040001e88c81e400ed8d888c80e1e1e400e4040400f40001e4000000000000000000000000030000040401f0d1f2d2d3d2d2d4d2d1e00000000000e2f4040000000000d394040401e1e0f000000000000000000000000000040000000000000000000000e400000001f00000e00001f00002d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 110:000000000e6a0050000e6a50001ed8d81e400e0e0e0e0f0e1e1e400e0e0e190f40001e000000000000000000000e400000000040401f1f1f00000000000000000000000000000e401e1e1e1e1e1e0040404000000f0000000000000000000000000000400000000000000000001e0e400000001f1f2d0e2d001f1f1f1f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 111:0000001f0e0e0e0e4d0e1f1f1e1e1e1e1e401e1e3d1e1e1e1e1e400e0f0f290f40401e580808080858585858580e000000000e40403e002d000000000000000000000000000000400000000000000040404000000f000000000000404040402d065606065606062d401e1e1e1e1e4d400000004d00000e00000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 112:00001f1f0000000000000000000000000040000000000000001e400e0000300000401e1e3d1e1e1e1e1e1e1e1e1e085808580f40402f001e000000000000000000000000000000400000000000000040404000000f000000000000000000002d585858585808582d4000000000000e400000001f00004d00003d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 113:001f1f000000000000000000000000000040000000000000001e400e0000000000401e000000001e3d000000001e1e3d1e1e1e1e1e1e403d0000000000000000000000000000002d000000005050000f404040400e00000000403d3d3d3d3d2d580858585858582d4000000000004d400000002d00000e0f2d0f2d2d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 114:1f1f000000000000000000000000000d0040000d00000000001e400e0000000000401e000000000e0e000000000000000000001e0000401e0000000000000000000000000000002d000000500000000f404040400e000000004000000000002d585858085808582d4000000000000e400000000000000e00003d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 115:1f00000000000000000000000000000e0d400d0e00000000001e400e0000000000401e000000000000000000000000000000001e0000403d0000000000000000002d4000000000400f0f191e1a3a0f0f404040400e000000004000000000002d2d2d2d2d2d2d2d2d40000000000d0e400000000000000e00003d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 116:1f0000000000000000000000000000003d0e0e0000000000001e400e400fd888c80f1e0e400e080808480e40000000000000001e400f1e1e0f0f0f0f2d0f0f000f0e1040000e404040403000200b3b00404040400e00000000400000000000000000000000000000400e0e0e0e1e1e1e4000000000002d1f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 117:000000000000000000000000000000000000000000000000001e400e000e0e0e0e0e0e0e400e585858580e40000000000000001e400f000000000000000000001e1e291e2d1f4d40404000000b4b2b00404040400e0000000040000000400000000000000000000040000000003d001e405050401e400e00001f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 118:000000000000000000000000000000000000000000000000001e400e000000000000000e400e3d0e0e0e0e40000000000000001e400f000000000000000000001e0030000e40001e0e2d000000000000404040400e1f1f1e1e1e1e1e1e400000000000000000000040000000003d401e1e1e191e1e400e00001f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 119:000000000000000000000000000000000000000000000000000e400e000000000000000e4000000000000040000000000000000e400000000000000000000000000000000e0040404040404040404040404040400e0000000000001e00400000000000000000000040000000003d401e2d2d391e2d402d2d3d1f3d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 120:0e00000000000000000000400e0e0e00500050400e0e0e40400e400e3e000000000000004000000000000040000000000000000e400000000000000000000000000000004d400040000000000000400e0e0e0e0e0e0000000000000000400000001e3d3d3d403d3d3d3d3d40403d401e1e1e09091e400e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 121:0e0e0e0e0e0e0000000000400e003d00005050400e000000400e400e2f0d00401f430303430e4000001d00400e3d4000400e400e400e00000000000000000000000000000e00400e5050505050000e0000000000000000000000000000400000001e0000004000000000000040004000000009091e400e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 122:000e0e0e4d0e0e0e0e0e0e0e0e000e00500000400e000000400e400e1f0e0e3d1f585858580e0e0e0e4d0e0e0e0e5111510e400e400e0e0e1e000000000e2d0e1e4040404d40000e5050505050004d000000000000000000000000000040000000001e000040000000001e00400040000000000000400e2d3d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 123:001e58581f581f5858580e0000000e40401000400e000000400e4000000000001e1e1e0e0e0e000000000000000e0e290e0e400e400e0e1e000000000e1e4d40404040400e00400e0e0e0e190e0e0e000000000000000000000000000040000000001e000040000000001e00400040000000000000000e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 124:00002d3d4d0f1f2d3d4d0e0000000e1a4a2a0e0e0e000000400e40003e00000000000000000e000000000000000000300000400e400e00000000000e1e404040404040400e00004040401a2a0000000000000e00000000000000000000400000000000000040000000002d0e400e0e0e401e480858082d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 125:000e0d0000000000001d3d00000000200000000000000000400e40002f00000000000000003d000000000000000000000000400e400000000000000000000000000000000e4040000000290e0000000000001e1e1e1e1e1e1e1e1e1e1e404040404040000040000000001e0040000000401e0e2d0e0e2d3d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 126:000e0e0000000000000e0e00000000200000000000000000404d0e1e1e4000000000400e400e00000000400e400000000000400e400000000000000000000000000000000e00000e4d0e390e000000000000000000000000000000000040000000001e1e0e0e0e4000001e0000000000401e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 127:001f1f190f190f190f0f0e0000000030000000400e4d0e0e0e0e00000eff00000000000f400e00000000400e04045454440e0e0e400e40000000000000000000000000002d0e0e0e0000000e00003e000000000000000000000000000040000000001e0000000040003d1e1e1e1e1e1e1e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 128:0e1f003000300030001e4d00000e465606460e0e0e000000400000000e0404040414040f404d005d0000400e08585808480e0000400e0e1e0e0e1e000e0e2d1e0f4040402d0000000000000e00002f000000000000000000000000000040000000001e000000004000001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 129:1e4d000000000000003d0000000e085858480e0000000000000000000e3d0e0e1e290f0f400e00000000404d0e0e0e4d0e0e0000400e0e2d0e1e0000000e1e40404040400e400000400e000000400e1e1e000000000000000000000000400000000000000000004000001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 130:1f1f00000000000000000000003d080808480e0000400e0e000e003e0000000000300000400e0e0e0e0040000000000000000e00400e00000000000000000000000000000e400000000eff0000004d00001e2d1e1e1e1e40000000401f1f1f1f1f40000000000040001e1e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 131:1e1f005d007e000000000000000e580858580e000040000e400e002f0000000000000000400e00000e0040000000000000000e00400000000000000000000000000000000e400000400e585858580e000000000000001f1f1f2d1f1f1f0000001f2d1e1e1e2d1e1e1e1e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 132:1f1f0040007f00000000000000000e0e0e0e4d0e0e400e0e400e0e0e0e0e400040000000000000000e004000000000403d3e0000400000000000000000000000000000000e400000000e080858080e00000000000000000000000000000000001f1f1f1f1f1f1f1f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 133:001f1f1f1f1f1f1f1f4d0e40000000000000000000400000400e0000000e445444540454545444040e004000000000401f2f0000400e40005d005d00000000001e00000000001f3d0e0e0e0e0e0e0e000000000000000000000000000000000000001f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 134:0000000000000000000e0e40000000000000000000400000401e000000000e0e0e1f1e1e1e4d0e0e0e0e0e0ec888d80e0e0e4d0e0e0e0000000000000000000f2d58585808581f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 135:000000000000000000000e0e0e0e0e4d0e0e0e0e0e0e0e0e0f000000000000000000000000000000000000000f0f0f000000000000001f1f1f1f4d1f1f1f1f1e1f1f1f2d1f1f1f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; </MAP1>

;; <WAVES>
;; 000:235689abcccddddccccccba986545550
;; 001:002406090b000e00000000000000eca8
;; 002:89c8e9fcf6ea751446479abb98389119
;; 006:00011233334455566678889aabbccdee
;; 008:fedccbaa998877665544443332221100
;; 009:246777888654556a6776534556679788
;; 012:00000000ffffffff00000000ffffffff
;; 013:0123456789abcdef0123456789abcdef
;; 014:0123456789abcdeffedcba9876543210
;; 015:777789abcdddddcba987654333456788
;; </WAVES>

;; <SFX>
;; 000:00e000f0029003a003b053b074cf85ce96dd97eca8eba9fa9af99af89bf99d0e9d0d8c0c8c0c8b0c7b0d7ccd6d0f6e006e016e036e036c046a056a0614500f0f0f0f
;; 001:000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000340000007b00
;; 002:000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005000000000
;; 003:0e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e00307000000000
;; 004:0d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d00000000000000
;; 006:091f093c092a092c09370936094709470934091209110901091109100910091009000900090009000900090009000900090009000900090009000900244061040000
;; 007:0d000d000d000d000d000d000d000d410d010d010d020d040d050d070d070d070d070d070d070d070d070d070d070d070d070d070d070d070d070d07300000000000
;; 008:0c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c00208000000000
;; 009:0e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e00309000000000
;; 010:0d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d000d00300000000000
;; 012:0f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00300000000000
;; 014:0e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e00000000000000
;; 015:0e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e00000000000000
;; 016:020002000200020002000200020002000200020002000200020002000200020002000200020002000200020002000200020002000200020002000200140000000000
;; </SFX>

;; <PATTERNS>
;; 000:b272c80000010000a0b000c80000c00000c00000a01000a00000a01000001000f01000a00000a01000a00000a06272c80000000000000000c06000c80000a00000010000000000000000a00000010000000000000000a01000000000a0100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 001:400001100020100020100001400001100020100060100020400001100040100020100020400001100020100020100040400001100000100000100000400001100000100000100000400001100000100000100000400001100000100000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 002:b000a41346a08000a4d106a41000a01000a07256a41000a06000a41000006000a61000a06146a81000a06000a41000a00000000000000000000000007000a41000000000000000004000a81000000000000000007000a4100000d000a21000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 003:b000f21346a08000f4d106f61000a01000a07256f61000a06000f41000006000f41000a06146f61000a06000f61000a00000000000000000000000007000f81000000000000000004000f61000000000000000007000f2100000d000f2100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; </PATTERNS>

;; <TRACKS>
;; 000:1803010008200000000000000000000000000000000000000000000000000000000000000000000000000000000000006f0200
;; </TRACKS>

;; <FLAGS>
;; 000:0090909020001818000000000000000040d0d0d0604058580212121222021a1a40d0d0d0604058580212121222021a1a40d0d0d0604058580212121222021a1a40d0d0d0604058580212121222021a1a40d0d0d0604058580212121222021a1a40d0d0d0604058580212121222021a1a40d0d0d0604058580212121222021a1a40d0d0d0604058581212121232121a1a009090900000181800000000000000009090909090a0180000000000000000009090909090a0a000000000000000000090909090900000000000000000000000040410101000000000000000000000001010000000000000000000000000000010100000000000000000000000000000
;; </FLAGS>

;; <PALETTE>
;; 000:0400005d275db13e53ef7d57ffcd75a7f07038b76425717929366f3b5dc941a6f673eff7f4f4f494b0c2566c86333c57
;; </PALETTE>

