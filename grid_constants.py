import enum

class ObjType(enum.Enum):
    CELL  = 1
    EDGE  = 2
    POINT = 3

CELL  = ObjType.CELL
EDGE  = ObjType.EDGE
POINT = ObjType.POINT

class Dir(enum.Enum):
    UP      = 1
    DOWN    = 2
    LEFT    = 3
    RIGHT   = 4

UP    = Dir.UP
DOWN  = Dir.DOWN
LEFT  = Dir.LEFT
RIGHT = Dir.RIGHT

VertDir = [UP, DOWN]
HorzDir = [LEFT, RIGHT]

class Orientation(enum.Enum):
    HORZ = 1
    VERT = 2

HORZ = Orientation.HORZ
VERT = Orientation.VERT

dir_preposition = {
    Dir.UP: "above",
    Dir.DOWN: "below",
    Dir.LEFT: "left",
    Dir.RIGHT: "right"
}

opposite_dir = {
    Dir.UP:    Dir.DOWN,
    Dir.DOWN:  Dir.UP,
    Dir.LEFT:  Dir.RIGHT,
    Dir.RIGHT: Dir.LEFT
}

# (dx, dy), origin top left
dir_deltas = {
    Dir.UP:    (0, -1),
    Dir.DOWN:  (0, 1),
    Dir.LEFT:  (-1, 0),
    Dir.RIGHT: (1, 0)
}
