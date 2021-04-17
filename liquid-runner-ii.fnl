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

(local player {:x 20 :y 20 :w 8 :h 16 :spr 256})
(local active-pipes [])

(local flags {:wall 0 :ladder 1 :water 2
              :vpipe 3 :hpipe 4})

;; water

(fn pipe-contains? [cx cy {: tiles}]
  (find-by tiles #(match $ [cx cy] true)))

(fn pipe-to [[px py] remaining]
  (assert (< 0 remaining) "pipe goes nowhere!")
  (if (fget (mget px (+ py 1)) flags.wall)
      [px py]
      (pipe-to [px (+ py 1)] (- remaining 1))))

(fn activate-pipe [cx cy]
  (let [tiles (doto (group cx cy flags.vpipe [])
                (table.sort #(< (. $1 2) (. $2 2))))
        [[top-x top-y]] tiles
        from (group top-x top-y flags.water [])
        to (pipe-to (last tiles) 99)
        key (xykey top-x top-y)]
    (tset active-pipes key {: tiles : key
                            : from : to :x top-x :y top-y})))

(fn toggle-pipe [cx cy] ; only vertical pipes for now
  (match (find-by active-pipes (partial pipe-contains? cx cy))
    pipe (tset active-pipes pipe.key nil)
    _ (activate-pipe cx cy)))

(fn tile-level [t] (// t 16))

(fn change-level [cx cy diff]
  (mset cx cy (+ (mget cx cy) (* diff 16))))

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

(fn drain-to [{:to [px py] &as pipe}]
  (if (and (fget (mget px py) flags.water)
           (= 8 (tile-level (mget px py))))
      (set pipe.to [px (- py 1)])
      (increase-level-across-row px py)))

(fn flow [pipe]
  (let [rows (group-by pipe.from #(. $ 2))
        [top-y] (doto (keys rows) (table.sort))
        top-tile (mget (table.unpack (. rows top-y 1)))
        level (tile-level top-tile)]
    (each [_ [tx ty] (ipairs (. rows top-y))]
      (change-level tx ty -1))
    (drain-to pipe)
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
                  [cx cy]
                  (touching x y flag (+ (or n 1) 1))))))

(fn inside? [{: x : y : w : h} flag]
  (or (fget (mget (// x 8) (// y 8)) flag)
      (fget (mget (// (+ x w -1) 8) (// y 8)) flag)
      (fget (mget (// x 8) (// (+ y h -1) 8)) flag)
      (fget (mget (// (+ x w -1) 8) (// (+ y h -1) 8)) flag)))

(fn stand-on? [{: x : y : w : h} flag]
  (or (fget (mget (// x 8) (// (+ y h) 8)) flag)
      (fget (mget (// (+ x w -1) 8) (// (+ y h) 8)) flag)))

(fn up-ok? [player]
  (or (inside? player flags.ladder)
      (fget (mget (// player.x 8) (+ (// player.y 8) 1))
            flags.water)))

(fn input []
  (let [{: x : y} player]
    (when (btn 2) (set player.x (+ player.x -1)))
    (when (btn 3) (set player.x (+ player.x +1)))
    (when (and (btn 0) (up-ok? player))
      (set player.y (+ player.y -1)))
    (when (and (btn 1) (stand-on? player flags.ladder))
      (set player.y (+ player.y +1)))
    ;; undo it if you try to move into a wall
    (when (inside? player flags.wall)
      (set player.x x)
      (set player.y y)))
  (when (btnp 4)
    (match (touching player.x player.y flags.vpipe)
      [cx cy] (toggle-pipe cx cy))))

(var t 0)

(fn update []
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
    (set player.y (+ player.y 1)))
  ;; water drains at a slower rate; only every 30 ticks
  (set t (math.fmod (+ t 1) 30))
  (when (= t 0)
    (each [_ pipe (pairs active-pipes)]
      (flow pipe))))

(fn draw []
  (map (- (// player.x 8) 14) (- (// player.y 8) 8)
       31 18
       (- (math.fmod player.x 8))
       (- (math.fmod player.y 8)))
  (spr player.spr 112 64 0 1 0 0 1 2))

(fn _G.TIC []
  (input)
  (update)
  (draw))

;; <TILES>
;; 001:5666666f5666666f056666f0056666f0056666f0056666f0056666f0056666f0
;; 002:056666f0056666f0056666f0056666f0056666f0056666f0056666f0056666f0
;; 003:056666f0056666f0056666f0056666f0056666f0056666f05666666f5666666f
;; 004:d000000dddddddddd000000dd000000dd000000dddddddddd000000dd000000d
;; 016:0000000000000000000000000000000000000000000000000000000088888888
;; 017:5666666f5666666f056666f0056666f0056666f0056666f0056666f0856666f8
;; 018:056666f0056666f0056666f0056666f0056666f0056666f0056666f0756666f8
;; 019:056666f0056666f0056666f0056666f0056666f0056666f05666666f5666666f
;; 020:d000000dddddddddd000000dd000000dd000000dddddddddd000000dd888888d
;; 032:0000000000000000000000000000000000000000000000008888888888888888
;; 033:5666666f5666666f056666f0056666f0056666f0056666f0856666f8856666f8
;; 034:056666f0056666f0056666f0056666f0056666f0056666f0856666f8856666f8
;; 035:056666f0056666f0056666f0056666f0056666f0056666f05666666f5666666f
;; 036:d000000dddddddddd000000dd000000dd000000dddddddddd888888dd888888d
;; 048:000000000000000000000000000000000000000088888aa88899888888888888
;; 049:5666666f5666666f056666f0056666f0056666f0856666f8856666f8856666f8
;; 050:056666f0056666f0056666f0056666f0056666f0856666f8856666f8856666f8
;; 051:056666f0056666f0056666f0056666f0056666f0856666f85666666f5666666f
;; 052:d000000dddddddddd000000dd000000dd000000dddddddddd888888dd888888d
;; 064:000000000000000000000000000000008888888888888aa88899888888888888
;; 065:5666666f5666666f056666f0056666f0856666f8856666f8856666f8856666f8
;; 066:056666f0056666f0056666f0056666f0856666f8856666f8856666f8856666f8
;; 067:056666f0056666f0056666f0056666f0856666f8856666f85666666f5666666f
;; 068:d000000dddddddddd000000dd000000dd888888dddddddddd888888dd888888d
;; 080:0000000000000000000000008888888888888888888889988899888888888888
;; 081:5666666f5666666f056666f0856666f8856666f8856666f8856666f8856666f8
;; 082:056666f0056666f0056666f0856666f8856666f8856666f8856666f8856666f8
;; 083:056666f0056666f0056666f0856666f8856666f8856666f85666666f5666666f
;; 084:d000000dddddddddd000000dd888888dd888888dddddddddd888888dd888888d
;; 096:0000000000000000888888888888888888888888888889988899888888888888
;; 097:5666666f5666666f856666f8856666f8856666f8856666f8856666f8856666f8
;; 098:056666f0056666f0856666f8856666f8856666f8856666f8856666f8856666f8
;; 099:056666f0056666f0856666f8856666f8856666f8856666f85666666f5666666f
;; 100:d000000dddddddddd888888dd888888dd888888dddddddddd888888dd888888d
;; 112:0000000088888888888888888888888888888888888889988899888888888888
;; 113:5666666f5666666f856666f8856666f8856666f8856666f8856666f8856666f8
;; 114:056666f0856666f8856666f8856666f8856666f8856666f8856666f8856666f8
;; 115:056666f0856666f8856666f8856666f8856666f8856666f85666666f5666666f
;; 116:d000000dddddddddd888888dd888888dd888888dddddddddd888888dd888888d
;; 128:8888888888888888888888888888888888888888888889988899888888888888
;; 129:5666666f5666666f856666f8856666f8856666f8856666f8856666f8856666f8
;; 130:856666f8856666f8856666f8856666f8856666f8856666f8856666f8856666f8
;; 131:856666f8856666f8856666f8856666f8856666f8856666f85666666f5666666f
;; 132:d888888dddddddddd888888dd888888dd888888dddddddddd888888dd888888d
;; 146:756666f7756666f7d56666fd756666f7756666f7756666f7d56666fd756666f7
;; 224:eeeedeeeeeeedeee66ddeddde6eeeeeee6eeeeeeedeeeeeeded66666eeee6eee
;; 225:eeee6eeeeeee6eee66ddeddde6eeeeeee6eeeeeeedeeeeeeded66666eeee6eee
;; 240:eeeedeeeeeeedeeed66deddde6eeeeeee6eeeeeeedeeeeeeded66666eeeedeee
;; 241:eeeedeeeeeeedeeeddddedddedeeeeeeedeeeeeeedeeeeeededdddddeeeedeee
;; </TILES>

;; <SPRITES>
;; 000:0444444004442440044444400444444004444440000400000044000000400000
;; 016:0044440044400040004000000044000000440000040440004400400040004000
;; </SPRITES>

;; <MAP>
;; 006:0000000000000000000000400e0e0e06060606460e0e0e40400e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 007:0000000000000000000000400e000e08080808480e000000400e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 008:00000e0e0e0e0e0e0e0e0e0e0e000e08080808480e000000400e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 009:00000e000000000000000e0000000e18080808480e000000400e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 010:00000e000000000000000e0000000e290e0e0e0e0e000000400e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 011:00000e000000000000000000000000200000000000000000400e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 012:00000e000000000000000000000000200000000000000000400e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 013:0000000000000000000000000000003000000040400e0e0e0e0e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 014:000000000000000000000000000e000000000e4040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 015:000000000000000000000000000e000000000e4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 016:000000000000000000000000000e000000000e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 017:000000000000000000000000000e000000000e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 018:000000000000000000000000000e0e0e0e0e0e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 019:000000000000000000000000000e0e0e0e0e0e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; </MAP>

;; <FLAGS>
;; 000:0090909020000000000000000000000040d0d0d060000000000000000000000040d0d0d060000000000000000000000040d0d0d060000000000000000000000040d0d0d060000000000000000000000040d0d0d060000000000000000000000040d0d0d060000000000000000000000040d0d0d060000000000000000000000040d0d0d060000000000000000000000000009000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001010000000000000000000000000000010100000000000000000000000000000
;; </FLAGS>

;; <PALETTE>
;; 000:0400005d275db13e53ef7d57ffcd75a7f07038b76425717929366f3b5dc941a6f673eff7f4f4f494b0c2566c86333c57
;; </PALETTE>

