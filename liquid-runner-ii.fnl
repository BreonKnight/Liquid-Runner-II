;; title: Liquid Runner II
;; author: breon knight / technomancy
;; desc: platform puzzler
;; script: fennel
;; input: gamepad
;; saveid: liquid-runner-ii

;; utility functions

(fn dbg [...] (trace (table.concat [...] " ")))
(fn pp [x] (trace ((. (require :fennel) :view) x)))

(fn xykey [x y] (.. x :x y))

(fn last [tbl] (. tbl (length tbl)))

(fn find [tbl x n]
  (match (. tbl (or n 1))
    x (or n 1)
    y (find tbl x (+ n 1))))

(fn find-by [tbl pred]
  (each [k v (pairs tbl)]
    (when (pred v k) (lua "return v, k"))))

(fn group-by [tbl f]
  (let [out {}]
    (each [_ x (ipairs tbl)]
      (let [key (f x)]
        (when (not (. out key)) (tset out key []))
        (table.insert (. out key) x)))
    out))

(fn keys [tbl] (icollect [k (pairs tbl)] k))

(local neighbors
       [[-1 -1] [0 -1] [1 -1]
        [-1 0] [1 0]
        [-1 1] [0 1] [1 1]])

(fn group [cx cy flag out]
  (each [_ [dx dy] (ipairs neighbors)]
    (let [nx (+ cx dx) ny (+ cy dy)]
      (when (and (fget (mget nx ny) flag)
                 (not (find-by out #(match $ [nx ny] true))))
        (table.insert out [nx ny])
        (group nx ny flag out))))
  out)

;; setup

(var t 0)
(local player {:x 20 :y 20 :w 8 :h 16 :spr 256})
(local active-pipes [])

(local flags {:wall 0 :ladder 1 :water 2
              :vpipe 3 :hpipe 4})

;; water

(fn pipe-contains? [cx cy {: tiles}]
  (find-by tiles #(match $ [cx cy] true)))

(local fennel (require :fennel))

(fn activate-pipe [cx cy]
  (let [tiles (doto (group cx cy flags.vpipe [])
                (table.sort #(< (. $1 2) (. $2 2))))
        [[top-x top-y]] tiles
        from (group top-x top-y flags.water [])
        key (xykey top-x top-y)]
    (tset active-pipes key {: tiles : key : from :x top-x :y top-y})))

(fn toggle-pipe [cx cy] ; only vertical pipes for now
  (match (find-by active-pipes (partial pipe-contains? cx cy))
    pipe (tset active-pipes pipe.key nil)
    _ (activate-pipe cx cy)))

(fn tile-level [t]
  (+ 1 (// t 16)))

(fn tile-for-level [level]
  (match level
    0 0
    _ (+ 3 (* (- level 1) 16))))

(fn flow [pipe]
  (let [rows (group-by pipe.from #(. $ 2))
        [top-y] (doto (keys rows) (table.sort))
        top-tile (mget (table.unpack (. rows top-y 1)))
        level (tile-level top-tile)]
    (each [_ [tx ty] (ipairs (. rows top-y))]
      (mset tx ty (tile-for-level (- level 1))))
    (when (= level 1)
      (set pipe.from (group pipe.x pipe.y flags.water []))
      (when (= 0 (length pipe.from))
        (tset active-pipes pipe.key nil)))))

;; movement logic

(local poffsets
       [[-1 -1] [0 -1] [1 -1]
        [-1 0] [0 0] [1 0]
        [-1 1] [0 1] [1 1]
        [-1 2] [0 2] [1 2]])

(fn touching [x y flag n]
  (match (. poffsets (or n 1))
    [ox oy] (let [cx (+ ox (// x 8)) cy (+ oy (// y 8))]
              (if (fget (mget cx cy) flag)
                  (values cx cy)
                  (touching x y flag (+ (or n 1) 1))))))

(fn inside? [{: x : y : w : h} flag]
  (or (fget (mget (// x 8) (// y 8)) flag)
      (fget (mget (// (+ x w -1) 8) (// y 8)) flag)
      (fget (mget (// x 8) (// (+ y h -1) 8)) flag)
      (fget (mget (// (+ x w -1) 8) (// (+ y h -1) 8)) flag)))

(fn stand-on? [{: x : y : w : h} flag]
  (or (fget (mget (// x 8) (// (+ y h) 8)) flag)
      (fget (mget (// (+ x w -1) 8) (// (+ y h) 8)) flag)))

(fn input []
  (let [{: x : y} player
        vertical? (or (inside? player flags.ladder)
                      (inside? player flags.water))]
    (when (btn 2) (set player.x (+ player.x -1)))
    (when (btn 3) (set player.x (+ player.x +1)))
    (when vertical?
      (when (btn 0) (set player.y (+ player.y -1)))
      (when (btn 1) (set player.y (+ player.y +1))))
    (when (inside? player flags.wall)
      (set player.x x)
      (set player.y y)))
  (when (btnp 4)
    (match (touching player.x player.y flags.vpipe)
      (cx cy) (toggle-pipe cx cy)))
  (when (btnp 5)
    (pp active-pipes)))

(fn update []
  (set t (math.fmod (+ t 1) 30))
  (when (and (not (stand-on? player flags.wall))
             (not (inside? player flags.water))
             (not (inside? player flags.ladder)))
    (set player.y (+ player.y 1)))
  (when (and (inside? player flags.water)
             (not (inside? player flags.ladder))
             (not (inside? player flags.wall))
             (< (math.random) 0.5))
    (set player.y (+ player.y 1)))
  (when (= t 0)
    (each [_ pipe (pairs active-pipes)]
      (flow pipe))))

(fn _G.TIC []
  (input)
  (update)
  (map)
  (spr player.spr player.x player.y 0 1 0 0 1 2))

;; <TILES>
;; 001:eeeedeeeeeeedeee66ddeddde6eeeeeee6eeeeeeedeeeeeeded66666eeee6eee
;; 002:d000000dddddddddd000000dd000000dd000000dddddddddd000000dd000000d
;; 003:0000000000000000000000000000000000000000000000000000000077777777
;; 004:5666666756666667056666700566667005666670056666700566667005666670
;; 005:5500000056555555566666665666666656666666566666665677777757000000
;; 006:0000000055555555666666666666666666666666666666667777777700000000
;; 007:0000005555555566666666666666666666666666666666667777776600000077
;; 017:eeeedeeeeeeedeeeddddedddedeeeeeeedeeeeeeedeeeeeededdddddeeeedeee
;; 018:d777777dddddddddd777777dd777777dd777777dddddddddd777777dd777777d
;; 019:0000000000000000000000000000000000000000000000007777777777777777
;; 020:0566667005666670056666700566667005666670056666700566667005666670
;; 035:0000000000000000000000000000000000000000777779977799777777777777
;; 036:0566667005666670056666700566667005666670056666705666666756666667
;; 051:0000000000000000000000000000000077777777777779977799777777777777
;; 067:0000000000000000000000007777777777777777777779977799777777777777
;; 083:0000000000000000777777777777777777777777777779977799777777777777
;; 099:0000000077777777777777777777777777777777777779977799777777777777
;; 115:7777777777777777777777777777777777777777777779977799777777777777
;; </TILES>

;; <SPRITES>
;; 000:0444444004442440044444400444444004444440000400000044000000400000
;; 016:0044440044400040004000000044000000440000040440004400400040004000
;; </SPRITES>

;; <MAP>
;; 005:001200000012001200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 006:000000000000001200120020101011313131312111111100201100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 007:000000000000000000000020100011373737372111000000201100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 008:000010101111111110101010100011373737371011000000201100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 009:000010000000000000001100000011403737371100000000201100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 010:000010000000000000001100000011411010111100000000201100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 011:000010000000000000001000000000410000000000000000201100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 012:000010000000000000000000000000410000000000000000201100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 013:000000000000000000000000000000420000002020111111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 014:000000000000000000000000001000000000102020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 015:000000000000000000000000001000000000102000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 016:000000000000000000000000001010101010100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; </MAP>

;; <FLAGS>
;; 000:00102040901111110000000000000000001020409000000000000000000000000000004090000000000000000000000000000040000000000000000000000000000000400000000000000000000000000000004000000000000000000000000000000040000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; </FLAGS>

;; <PALETTE>
;; 000:0400005d275db13e53ef7d57ffcd75a7f07038b76425717929366f3b5dc941a6f673eff7f4f4f494b0c2566c86333c57
;; </PALETTE>

