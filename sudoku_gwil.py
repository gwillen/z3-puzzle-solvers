import sys
import z3
import pygame
from solver import *
import grid
import display
import adjacency_manager

givens = [
  [7, 0, 3,  0, 0, 0,  0, 0, 6],
  [0, 1, 0,  0, 0, 9,  0, 0, 0],
  [0, 9, 6,  1, 0, 0,  0, 3, 0],

  [5, 0, 0,  0, 0, 7,  9, 0, 4],
  [0, 0, 0,  8, 1, 0,  2, 0, 0],
  [0, 0, 0,  5, 0, 0,  0, 0, 0],

  [0, 0, 2,  4, 0, 0,  0, 0, 8],
  [0, 0, 0,  0, 0, 0,  0, 0, 0],
  [3, 0, 4,  0, 0, 0,  0, 6, 0]]

"""
givens = [
  "7 3     6",
  " 1   9   ",
  " 961   3 ",

  "5    79 4",
  "   81 2  ",
  "   5     ",

  "  24    8",
  "         ",
  "3 4    6 "]
"""

m = None
g = None

def solve_sudoku(givens):
    global m, g

    clear_context()
    g = grid.Grid(width=9, height=9)

    def init_cell(cell):
        var =  IntRangeVar(cell.name, min=1, max=9)
        if cell.given:
            # would be nice if we could do this automatically but "given" can mean so many things
            # XXX eww, abstraction break.
            ASSERT(var.var == cell.given)
        return var

    # TK: init_edges, init_points
    # creates cell.given, cell.var
    g.init_cells(givens, init_cell)

    for group in g.cell_rows() + g.cell_cols() + g.cell_boxes(3, 3):
        DISTINCT([cell.var for cell in group])

    m = get_model()
    next_model()
    return not solvable()

def cell_draw(ctx):
    ctx.fill(0.9, 0.9, 1, 1)

    given = ctx.cell.given
    given_str = "" if given == 0 else str(given)
    color = (0, 0, 0, 1)
    if (given):
        color = (1, 0, 0, 1)

    ctx.text(ctx.val or given_str, fontsize=40, color=color)

def edge_draw(ctx):
    ctx.draw(width=2)

def point_draw(ctx):
    pass

#XXX haxxxx
click_x = None
click_y = None

def process_events(events):
    global click_x, click_y

    result = False
    for event in events:
        if event.type == pygame.QUIT:
            sys.exit(0)
        elif event.type == pygame.KEYDOWN:
            if event.key == 27:
                sys.exit(0)
        if event.type == pygame.MOUSEBUTTONUP:
            print("mouse up: " + str(event.pos))
            click_x = (event.pos[0] - 35) // 64
            click_y = (event.pos[1] - 35) // 64
            result = True
        else:
            print(event)
    return result

pygame.init()

solve_sudoku(givens)
surface = display.draw_grid(g, m, 64, cell_draw, edge_draw, edge_draw, point_draw)

width = surface.get_width()
height = surface.get_height()

pygame.display.set_mode((width, height))

screen = pygame.display.get_surface()

while True:
    surface = display.draw_grid(g, m, 64, cell_draw, edge_draw, edge_draw, point_draw)
    buf = surface.get_data()
    # TODO: color management is a little funny, probably due to pixel
    # formats here. In a bunch of places we need to call rgb functions
    # but pass things in in g, b, r order.
    image = pygame.image.frombuffer(buf, (width, height), "RGBA")
    # Tranfer to Screen
    screen.blit(image, (0, 0))
    pygame.display.flip()

    if process_events(pygame.event.get()):
        givens[click_y][click_x] = (givens[click_y][click_x] + 1) % 10
        unique = solve_sudoku(givens)
