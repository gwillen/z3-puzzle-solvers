from typing import Dict, List, Union, Optional, Tuple, cast

import solver
from grid_constants import *

class BoardObj(object):
    def __init__(self, name: str):
        self.neighbors: Dict[ObjType, Dict[Dir, BoardObj]] = {}
        self.name = name

    def obj_at(self, obj_type: ObjType, direction: Dir, dist: int) -> 'Optional[BoardObj]':
        if obj_type not in ObjType:
            raise ValueError("Bad objtype: " + str(obj_type))
        if direction not in Dir:
            raise ValueError("Bad direction: " + str(direction))
        if dist < 0:
            # Let's just be nice and fix it.
            return self.obj_at(obj_type, opposite_dir[direction], -dist)
        elif dist == 0:
            return self
        elif self.neighbors[obj_type][direction]:
            return self.neighbors[obj_type][direction].obj_at(obj_type, direction, dist-1)
        else:
            return None

    def obj(self, obj_type: ObjType, direction: Dir) -> 'Optional[BoardObj]':
        return self.obj_at(obj_type, direction, 1)

    def cell_at(self, direction: Dir, dist: int) -> 'Optional[Cell]':
        return cast(Cell, self.obj_at(ObjType.CELL, direction, dist))
    def edge_at(self, direction: Dir, dist: int) -> 'Optional[Edge]':
        return cast(Edge, self.obj_at(ObjType.EDGE, direction, dist))
    def point_at(self, direction: Dir, dist: int) -> 'Optional[Point]':
        return cast(Point, self.obj_at(ObjType.POINT, direction, dist))

    def cells(self) -> 'List[Cell]':
        return cast(List[Cell], self.neighbors[ObjType.CELL].values())
    def edges(self) -> 'List[Edge]':
        return cast(List[Edge], self.neighbors[ObjType.EDGE].values())
    def points(self) -> 'List[Point]':
        return cast(List[Point], self.neighbors[ObjType.POINT].values())

class Cell(BoardObj):
    def __init__(self, name: str, *, x: int, y: int):
        super().__init__(name)
        self.x = x
        self.y = y
        self.neighbors = { ObjType.EDGE: {}, ObjType.CELL: {} }
        self.edge = cast(Dict[Dir, Optional[Edge]], self.neighbors[ObjType.EDGE])
        self.cell = cast(Dict[Dir, Optional[Cell]], self.neighbors[ObjType.CELL])

    def __str__(self) -> str:
        return "Cell({} @ {}, {})".format(self.name, self.x, self.y)

class Edge(BoardObj):
    def __init__(self, name: str, *, orientation: Orientation, x: int, y: int):
        super().__init__(name)
        self.orientation = orientation
        self.x = x
        self.y = y
        self.neighbors = { ObjType.CELL: {}, ObjType.EDGE: {}, ObjType.POINT: {} }
        self.edge = cast(Dict[Dir, Optional[Edge]], self.neighbors[ObjType.EDGE])
        self.cell = cast(Dict[Dir, Optional[Cell]], self.neighbors[ObjType.CELL])
        self.point = cast(Dict[Dir, Optional[Point]], self.neighbors[ObjType.POINT])

    def __str__(self) -> str:
        return "Edge/{}({})".format(self.orientation, self.name)

class Point(BoardObj):
    def __init__(self, name: str, *, x: int, y: int):
        super().__init__(name)
        self.x = x
        self.y = y
        self.neighbors = { ObjType.EDGE: {}, ObjType.POINT: {} }
        self.edge = cast(Dict[Dir, Optional[Edge]], self.neighbors[ObjType.EDGE])
        self.point = cast(Dict[Dir, Optional[Point]], self.neighbors[ObjType.POINT])

    def horiz_edge(self, offs: int) -> Optional[Edge]:
        assert offs != 0
        return self.edge_at(Dir.RIGHT, offs)

    def vert_edge(self, offs: int) -> Optional[Edge]:
        assert offs != 0
        return self.edge_at(Dir.DOWN, offs)

    def __str__(self) -> str:
        return "Point({} @ {}, {})".format(self.name, self.x, self.y)

class Grid(object):
    # NB: width and height are in cells
    def __init__(self, *, width: int, height: int, basename: str = ''):
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
                e = Edge(name, orientation=Orientation.VERT, x=x, y=y)
                verts.append(e)
                vert_array[x,y] = e

        self.vert_array = vert_array
        self.verts = verts

        for x in range(width):
            for y in range(height+1):
                name = '{}horiz_{},{}'.format(basename, x, y)
                e = Edge(name, orientation=Orientation.HORZ, x=x, y=y)
                horizs.append(e)
                horiz_array[x,y] = e

        self.horiz_array = horiz_array
        self.horizs = horizs

        for x in range(width+1):
            for y in range(height+1):
                name = '{}point_{},{}'.format(basename, x, y)
                p = Point(name, x=x, y=y)
                points.append(p)
                point_array[x, y] = p

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

    def cell(self, x: int, y: int) -> Optional[Cell]:
        return self.cell_array.get((x, y))

    def horiz(self, x: int, y: int) -> Optional[Edge]:
        return self.horiz_array.get((x, y))

    def vert(self, x: int, y: int) -> Optional[Edge]:
        return self.vert_array.get((x, y))

    def point(self, x: int, y: int) -> Optional[Point]:
        return self.point_array.get((x, y))

    def cell_rows(self) -> List[List[Cell]]:
        return [[self.cell_array[x, y] for x in range(0, self.height)] for y in range(0, self.width)]

    def cell_cols(self) -> List[List[Cell]]:
        return [[self.cell_array[x, y] for y in range(0, self.height)] for x in range(0, self.width)]

    # Parameters are box SIZE not box COUNT!
    def cell_boxes(self, box_height: int, box_width: int) -> List[List[Cell]]:
        if ((box_height < 1 or box_height > self.height or self.height % box_height != 0) or
            (box_width  < 1 or box_width  > self.width  or self.width  % box_width  != 0)):
            raise Exception("Box size rows/cols must divide board height/width")

        box_rows = self.height // box_height
        box_cols = self.width // box_width

        return [[
            self.cell(box_x * box_width + inner_x, box_y * box_height + inner_y)
                for inner_y in range(0, box_height) for inner_x in range(0, box_width)]
                    for box_y in range(0, box_rows) for box_x in range(0, box_cols)]

    def cells_locs(self) -> List[Tuple[Cell, int, int]]:
        return [(self.cell(x, y), x, y) for y in range(0, self.height) for x in range(0, self.width)]

    def format_given_char(self, c: str) -> Union[int, str]:
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
