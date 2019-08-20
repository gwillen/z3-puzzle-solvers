import z3
import enum

class ObjType(enum.Enum):
    CELL  = 1
    EDGE  = 2
    POINT = 3
# super rude, omg
locals().update(ObjType.__members__)

class Dir(enum.Enum):
    UP      = 1
    DOWN    = 2
    LEFT    = 3
    RIGHT   = 4
# super rude, omg
locals().update(Dir.__members__)

VertDir = [UP, DOWN]
HorzDir = [LEFT, RIGHT]

class Orientation(enum.Enum):
    HORZ = 1
    VERT = 2
# super rude, omg
locals().update(Orientation.__members__)

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

# For synthesizing convenience functions "edge_above", "cell_left" etc.
#def neighbor_prop(types, d):
#    def get_neighbor(self):
#        return getattr(self, "neighbor_"+types).get(d)
#    def set_neighbor(self, v):
#        getattr(self, "neighbor_"+types)[d] = v
#    return(property(get_neighbor, set_neighbor))

#XXX broken: def distant_neighbor_prop(types, d):
#    def get_distant_neighbor(self, distance):
#        return getattr(self, "get_neighbor_"+type+"_at")()

class BoardObj(object):
    def __init__(self, name):
        self.neighbors = {}
        self.name = name

    def obj_at(self, obj_type, direction, dist):
        if obj_type not in ObjType:
            raise Error("Bad objtype: " + str(obj_type))
        if direction not in Dir:
            raise Error("Bad direction: " + str(direction))
        if dist < 0:
            # Let's just be nice and fix it.
            return self.obj_at(obj_type, opposite_dir[direction], -dist)
        elif dist == 0:
            return self
        else:
            return neighbors[obj_type][direction].obj_at(obj_type, direction, dist-1)

    def obj(self, obj_type, direction):
        return self.obj_at(obj_type, direction, 1)

    def cell_at(self, direction, dist):
        return obj_at(ObjType.CELL, direction, dist)
    def edge_at(self, direction, dist):
        return obj_at(ObjType.EDGE, direction, dist)
    def point_at(self, direction, dist):
        return obj_at(ObjType.POINT, direction, dist)

    def cell(self, direction):
        return adj_obj(ObjType.CELL, direction)
    def edge(self, direction):
        return adj_obj(ObjType.EDGE, direction)
    def point(self, direction):
        return adj_obj(ObjType.POINT, direction)

class Cell(BoardObj):
    def __init__(self, name, *, x, y):
        super().__init__(name)
        self.x = x
        self.y = y
        self.neighbors = { ObjType.EDGE: {}, ObjType.CELL: {} }
        self.edge = self.neighbors[ObjType.EDGE]
        self.cell = self.neighbors[ObjType.CELL]

    def edges(self):
        return self.edge.values()

    def cells(self):
        return self.cell.values()

    def __str__(self):
        return "Cell({} @ {}, {})".format(self.name, self.x, self.y)

#for direction in Dir:
#    setattr(Cell,
#        "edge_"+dir_preposition[direction],
#        neighbor_prop("edges", direction))
#    setattr(Cell,
#        "cell_"+dir_preposition[direction],
#        neighbor_prop("cells", direction))

class Edge(BoardObj):
    def __init__(self, name, *, orientation, x, y):
        super().__init__(name)
        self.orientation = orientation
        self.x = x
        self.y = y
        self.neighbors = { ObjType.CELL: {}, ObjType.EDGE: {}, ObjType.POINT: {} }
        self.edge = self.neighbors[ObjType.EDGE]
        self.cell = self.neighbors[ObjType.CELL]
        self.point = self.neighbors[ObjType.POINT]

    def cells(self):
        return self.neighbors[ObjType.CELL].values()

    def points(self):
        return self.neighbors[ObjType.POINT].values()

    def __str__(self):
        return "Edge/{}({})".format(self.orientation, self.name)

# This doesn't distinguish vertical from horizontal edges as the old code did.
#for direction in Dir:
#    setattr(Edge,
#        "edge_"+dir_preposition[direction],
#        neighbor_prop("edges", direction))
#    setattr(Edge,
#        "cell_"+dir_preposition[direction],
#        neighbor_prop("cells", direction))
#    setattr(Edge,
#        "point"+dir_preposition[direction],
#        neighbor_prop("points", direction))

class Point(BoardObj):
    def __init__(self, name, *, x, y):
        super().__init__(name)
        self.x = x
        self.y = y
        self.neighbors = { ObjType.EDGE: {}, ObjType.POINT: {} }
        self.edge = self.neighbors[ObjType.EDGE]
        self.point = self.neighbors[ObjType.POINT]

    def edges(self):
        return self.edge.values()

    def points(self):
        return self.point.values()

    def horiz_edge(self, offs):
        assert offs != 0
        return self.edge_at(Dir.RIGHT, offs)

    def vert_edge(self, offs):
        assert offs != 0
        return self.edge_at(Dir.DOWN, offs)

    def __str__(self):
        return "Point({} @ {}, {})".format(self.name, self.x, self.y)

class Grid(object):
    # NB: width and height are in cells
    def __init__(self, *, width, height, basename=''):
        self.width = width
        self.height = height

        cell_array = {}
        vert_array = {}
        horiz_array = {}
        point_array = {}

        cells = []
        verts = []
        horizs = []
        points = []

        for x in range(width):
            for y in range(height):
                name = '{}cell_{},{}'.format(basename, x, y)
                c = Cell(name, x=x, y=y)
                cells.append(c)
                cell_array[x,y] = c

        self.cell_array = cell_array
        self.cells = cells

        for x in range(width+1):
            for y in range(height):
                name = '{}vert_{},{}'.format(basename, x, y)
                c = Edge(name, orientation=Orientation.VERT, x=x, y=y)
                verts.append(c)
                vert_array[x,y] = c

        self.vert_array = vert_array
        self.verts = verts

        for x in range(width):
            for y in range(height+1):
                name = '{}horiz_{},{}'.format(basename, x, y)
                c = Edge(name, orientation=Orientation.HORZ, x=x, y=y)
                horizs.append(c)
                horiz_array[x,y] = c

        self.horiz_array = horiz_array
        self.horizs = horizs

        for x in range(width+1):
            for y in range(height+1):
                name = '{}point_{},{}'.format(basename, x, y)
                c = Point(name, x=x, y=y)
                points.append(c)
                point_array[x, y] = c

        self.point_array = point_array
        self.points = points

        for x in range(width):
            for y in range(height):
                c = cell_array[x,y]
                c.cell[UP] = self.cell(x,y-1)
                c.cell[DOWN] = self.cell(x,y+1)
                c.cell[LEFT] = self.cell(x-1,y)
                c.cell[RIGHT] = self.cell(x+1,y)

                c.edge[UP] = self.horiz(x, y)
                c.edge[UP].cell[DOWN] = c
                c.edge[DOWN] = self.horiz(x, y+1)
                c.edge[DOWN].cell[UP] = c
                c.edge[LEFT] = self.vert(x, y)
                c.edge[LEFT].cell[RIGHT] = c
                c.edge[RIGHT] = self.vert(x+1, y)
                c.edge[RIGHT].cell[LEFT] = c

        for x in range(width+1):
            for y in range(height):
                e = self.vert(x, y)
                e.edge[UP] = self.vert(x, y-1)
                e.edge[DOWN] = self.vert(x, y+1)

        for x in range(width):
            for y in range(height+1):
                e = self.horiz(x, y)
                e.edge[LEFT] = self.horiz(x-1, y)
                e.edge[RIGHT] = self.horiz(x+1, y)

        for x in range(width+1):
            for y in range(height+1):
                p = self.point(x, y)
                for d in HorzDir:
                    xdelta = -1 if d == LEFT else 0  # deal with grid alignment
                    p.edge[d] = self.horiz(x + xdelta, y)
                    if p.edge[d]:
                        p.edge[d].point[opposite_dir[d]] = p
                for d in VertDir:
                    ydelta = -1 if d == UP else 0  # deal with grid alignment
                    p.edge[d] = self.vert(x, y + ydelta)
                    if p.edge[d]:
                        p.edge[d].point[opposite_dir[d]] = p
                for d in Dir:
                    (dx, dy) = dir_deltas[d]
                    p.point[d] = self.point(x + dx, y + dy)

    def cell(self, x, y):
        return self.cell_array.get((x, y))

    def horiz(self, x, y):
        return self.horiz_array.get((x, y))

    def vert(self, x, y):
        return self.vert_array.get((x, y))

    def point(self, x, y):
        return self.point_array.get((x, y))

    def cell_rows(self):
        return [[self.cell_array[x, y] for x in range(0, self.height)] for y in range(0, self.width)]

    def cell_cols(self):
        return [[self.cell_array[x, y] for y in range(0, self.height)] for x in range(0, self.width)]

    # Parameters are box SIZE not box COUNT!
    def cell_boxes(self, box_height, box_width):
        if ((box_height < 1 or box_height > self.height or self.height % box_height != 0) or
            (box_width  < 1 or box_width  > self.width  or self.width  % box_width  != 0)):
            raise Exception("Box size rows/cols must divide board height/width")

        box_rows = self.height // box_height
        box_cols = self.width // box_width

        return [[
            self.cell(box_x * box_width + inner_x, box_y * box_height + inner_y)
                for inner_y in range(0, box_height) for inner_x in range(0, box_width)]
                    for box_y in range(0, box_rows) for box_x in range(0, box_cols)]

    def cells_locs(self):
        return [(self.cell(x, y), x, y) for y in range(0, self.height) for x in range(0, self.width)]

    def format_given_char(self, c):
        if (c >= '0' and c <= '9'):
            return ord(c) - ord('0')
        if (c == ' '):
            return None
        return c

    # reshape an array, string, array-of-arrays, or array-of-strings, into what we want.
    def format_givens(self, givens):
        if type(givens) == str:
            if len(givens) == self.width * self.height:
                givens = [self.format_given_char(c) for c in givens]
                return [givens[i : i+self.width] for i in range(0, len(givens), self.width)]
            else:
                raise Exception("Givens bad shape")
        elif type(givens) == list:
            if len(givens) == self.width * self.height:
                return [givens[i : i+self.width] for i in range(0, len(givens), self.width)]
            elif len(givens) == self.height:
                if not all(len(row) == self.width for row in givens):
                    raise Exception("Givens bad shape")

                if all(type(row) == str for row in givens):
                    return [[self.format_given_char(c) for c in row] for row in givens]
                elif all(type(row) == list for row in givens):
                    return givens
                else:
                    raise Exception("Givens mixed types")
        else:
            raise Exception("Givens unknown type")

    def init_cells(self, givens, initfn):
        givens = self.format_givens(givens)
        for (cell, x, y) in self.cells_locs():
            cell.given = givens[y][x]
            cell.var = initfn(cell)

    @property
    def edges(self):
        return self.horizs + self.verts

# g = EdgedGrid(10, 10)

# s = Solver()

# for c in g.cells:
#     s.add(c.var >= 0)
#     s.add(c.var < 10)

# #for x in range(10):
# #    s.add(Distinct([g.cell(x, y).var for y in range(10)]))
# #    s.add(Distinct([g.cell(y, x).var for y in range(10)]))

# s.check()
# m = s.model()
# for x in list(m):
#     print m[x]
# for y in range(10):
#     r = ""
#     for x in range(10):
#         r += str(m[g.cell(x, y).var].as_long())
#     print r
