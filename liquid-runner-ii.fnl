;; title: Liquid Runner II
;; author: breon knight / technomancy
;; desc: platform puzzler
;; script: fennel
;; input: gamepad
;; saveid: liquid-runner-ii

;; utility functions

(fn find [tbl x n]
  (match (. tbl (or n 1))
    x n
    y (find tbl x (+ n 1))))

;; setup

(local player {:x 20 :y 20 :w 8 :h 16 :spr 256})
(local flags {:wall 0 :ladder 1 :water 2
              :vpipe 3 :hpipe 4})

;; movement logic

(fn inside? [{: x : y : w : h} flag]
  (or (fget (mget (// x 8) (// y 8)) flag)
      (fget (mget (// (+ x w -1) 8) (// y 8)) flag)
      (fget (mget (// x 8) (// (+ y h -1) 8)) flag)
      (fget (mget (// (+ x w -1) 8) (// (+ y h -1) 8)) flag)))

(fn stand-on? [{: x : y : w : h} flag]
  (or (fget (mget (// x 8 -1) (// (+ y h) 8)) flag)
      (fget (mget (// (+ x w -1) 8) (// (+ y h) 8)) flag)))

(fn move []
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
      (set player.y y))))

(fn update []
  (when (and (not (stand-on? player flags.solid))
             (not (inside? player flags.water))
             (not (inside? player flags.ladder)))
    (set player.y (+ player.y 1)))
  (when (and (inside? player flags.water)
             (not (inside? player flags.ladder))
             (not (inside? player flags.wall))
             (< (math.random) 0.5))
    (set player.y (+ player.y 1))))

(fn _G.TIC []
  (move)
  (update)
  (map)
  (spr player.spr player.x player.y 0 1 0 0 1 2))

;; <TILES>
;; 001:eeeedeeeeeeedeee66ddeddde6eeeeeee6eeeeeeedeeeeeeded66666eeee6eee
;; 002:d000000dddddddddd000000dd000000dd000000dddddddddd000000dd000000d
;; 003:7777777777777777799997777777777777777777777999977777777777777777
;; 004:5666666756666667056666700566667005666670056666700566667005666670
;; 005:5500000056555555566666665666666656666666566666665677777757000000
;; 006:0000000055555555666666666666666666666666666666667777777700000000
;; 007:0000005555555566666666666666666666666666666666667777776600000077
;; 017:eeeedeeeeeeedeeeddddedddedeeeeeeedeeeeeeedeeeeeededdddddeeeedeee
;; 018:d777777dddddddddd777777dd777777dd777777dddddddddd777777dd777777d
;; 019:7777777777777779799999777777777777777777777779977799777777777777
;; 020:0566667005666670056666700566667005666670056666700566667005666670
;; 036:0566667005666670056666700566667005666670056666705666666756666667
;; </TILES>

;; <SPRITES>
;; 000:0444444004442440044444400444444004444440000400000044000000400000
;; 016:0044440044400040004000000044000000440000040440004400400040004000
;; </SPRITES>

;; <MAP>
;; 005:001200000012001200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 006:000000000000001200120020101011303031302111111100201100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 007:000000000000000000000020100011303130302111000000201100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 008:000010101111111110101010100011303130311011000000201100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 009:000010000000000000001100000011403030311100000000201100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 010:000010000000000000001100000011411010111100000000201100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 011:000010000000000000001000000000410000000000000000201100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 012:000010000000000000000000000000410000000000000000201100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 013:000000000000000000000000000000420000002020111111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 014:000000000000000000000000001000000000102020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 015:000000000000000000000000001000000000102000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; 016:000000000000000000000000001010101010100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; </MAP>

;; <FLAGS>
;; 000:00102040901111110000000000000000001020409000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
;; </FLAGS>

;; <PALETTE>
;; 000:0400005d275db13e53ef7d57ffcd75a7f07038b76425717929366f3b5dc941a6f673eff7f4f4f494b0c2566c86333c57
;; </PALETTE>

