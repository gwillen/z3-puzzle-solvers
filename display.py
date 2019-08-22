import math
import sys
import os

import cairo

def font(family='', bold=False, italic=False):
    return cairo.ToyFontFace(
        family,
        cairo.FontSlant.ITALIC if italic else cairo.FontSlant.NORMAL,
        cairo.FontWeight.BOLD if bold else cairo.FontWeight.NORMAL,
    )

with open(os.devnull, 'w') as f:
    # disable stdout
    oldstdout = sys.stdout
    sys.stdout = f

    import pygame

    # enable stdout
    sys.stdout = oldstdout

def transform_x(x, scale):
    return scale/2 + x * scale

def transform_y(y, scale):
    return scale/2 + y * scale

def canvas_size(w, h, scale):
    return (w+1) * scale, (h+1) * scale

class PointContext(object):
    def __init__(self, surface, point, model, scale):
        self.surface = surface
        self.point = point
        self.model = model
        self.scale = scale
        self.ctx = cairo.Context(surface)

    @property
    def val(self):
        if model is not none:
            return str(self.model[self.point.var])
        else:
            return ""

    @property
    def x0(self):
        return transform_x(self.gx, self.scale)

    @property
    def y0(self):
        return transform_y(self.gy, self.scale)

    @property
    def gx(self):
        return self.point.x

    @property
    def gy(self):
        return self.point.y

    def draw_square(self, size=1, color=(0, 0, 0, 1)):
        r, g, b, a = color
        self.ctx.set_source_rgba(b, g, r, a)
        self.ctx.rectangle(self.x0 - size/2, self.y0 - size/2,
                           size, size)
        self.ctx.fill()

    def draw_circle(self, size=10, color=(0, 0, 0, 1), fill=False):
        r, g, b, a = color
        self.ctx.set_source_rgba(b, g, r, a)
        self.ctx.arc(self.x0, self.y0, size, 0, 6.3)
        if fill:
            self.ctx.fill()
        else:
            self.ctx.stroke()

class EdgeContext(object):
    def __init__(self, surface, edge, model, scale):
        self.surface = surface
        self.edge = edge
        self.model = model
        self.scale = scale
        self.ctx = cairo.Context(surface)

    @property
    def val(self):
        if model is not None:
            return str(self.model[self.edge.var])
        else:
            return ""

    @property
    def x0(self):
        return transform_x(self.gx, self.scale)

    @property
    def y0(self):
        return transform_y(self.gy, self.scale)

    @property
    def gx(self):
        return self.edge.x

    @property
    def gy(self):
        return self.edge.y

    def draw(self, width=1, color=(0, 0, 0, 1)):
        self.ctx.set_line_width(width)
        r, g, b, a = color
        self.ctx.set_source_rgba(b, g, r, a)
        self.ctx.move_to(self.x0, self.y0)
        self.ctx.line_to(self.x1, self.y1)
        self.ctx.stroke()

class HorizEdgeContext(EdgeContext):
    def __init__(self, *a, **kw):
        super(HorizEdgeContext, self).__init__(*a, **kw)

    @property
    def x1(self):
        return transform_x(self.gx + 1, self.scale)

    @property
    def y1(self):
        return self.y0

class VertEdgeContext(EdgeContext):
    def __init__(self, *a, **kw):
        super(VertEdgeContext, self).__init__(*a, **kw)

    @property
    def x1(self):
        return self.x0

    @property
    def y1(self):
        return transform_y(self.gy + 1, self.scale)

class CellContext(object):
    def __init__(self, surface, cell, model, scale):
        self.surface = surface
        self.ctx = cairo.Context(surface)
        self.cell = cell
        self.model = model
        self.scale = scale

    @property
    def val(self):
        if self.model is not None:
            return str(self.model[self.cell.var])
        else:
            return ""

    @property
    def x0(self):
        return transform_x(self.gx, self.scale)

    @property
    def x1(self):
        return transform_x(self.gx + 1, self.scale)

    @property
    def y0(self):
        return transform_y(self.gy, self.scale)

    @property
    def y1(self):
        return transform_y(self.gy + 1, self.scale)

    @property
    def mx(self):
        return transform_x(self.gx + 0.5, self.scale)

    @property
    def my(self):
        return transform_y(self.gy + 0.5, self.scale)

    @property
    def gx(self):
        return self.cell.x

    @property
    def gy(self):
        return self.cell.y

    def fill(self, r, g, b, a):
        self.ctx.set_source_rgba(b, g, r, a)
        self.ctx.rectangle(self.x0, self.y0, self.scale, self.scale)
        self.ctx.fill()

    def text(self, text, fontsize=12, family='', bold=False, italic=False, color=(0, 0, 0, 1)):
        self.ctx.set_font_size(fontsize)
        self.ctx.set_font_face(font(family, bold, italic))
        r, g, b, a = color
        self.ctx.set_source_rgba(b, g, r, a)
        draw_text(self.ctx, self.mx, self.my, text)
        self.ctx.stroke()

    def circle(self, size=None, color=(0, 0, 0, 1), fill=False):
        # TODO: consistent name (circle vs. draw_circle)
        if not size:
            size = self.scale/2.3
        r, g, b, a = color
        self.ctx.set_source_rgba(b, g, r, a)
        self.ctx.arc(self.mx, self.my, size, 0, 6.3)
        if fill:
            self.ctx.fill()
        else:
            self.ctx.stroke()

def draw_grid(grid, model, scale,
              cell_fn=None, horiz_fn=None, vert_fn=None,
              point_fn=None):
    canvas_w, canvas_h = canvas_size(grid.width, grid.height, scale)
    surface = get_surface(canvas_w, canvas_h)

    if cell_fn:
        for cell in grid.cells:
            cell_ctx = CellContext(surface, cell, model, scale)
            cell_fn(cell_ctx)
    if horiz_fn:
        for horiz in grid.horizs:
            horiz_ctx = HorizEdgeContext(surface, horiz, model, scale)
            horiz_fn(horiz_ctx)
    if vert_fn:
        for vert in grid.verts:
            vert_ctx = VertEdgeContext(surface, vert, model, scale)
            vert_fn(vert_ctx)
    if point_fn:
        for point in grid.points:
            point_ctx = PointContext(surface, point, model, scale)
            point_fn(point_ctx)
    return surface
    #XXX show_surface(surface)

def draw_text(ctx, x, y, t):
    _, _, w, h, dx, dy = ctx.text_extents(t)
    ctx.move_to(x - w/2, y + h/2)
    ctx.show_text(t)

def process_events(events):
    for event in events:
        if event.type == pygame.QUIT:
            sys.exit(0)
        elif event.type == pygame.KEYDOWN:
            if event.key == 27:
                sys.exit(0)
        if event.type == pygame.MOUSEBUTTONUP:
            print("mouse up: " + str(event.pos))
        else:
            print(event)

def get_surface(width, height):
    surface = cairo.ImageSurface(cairo.FORMAT_ARGB32, width, height)
    ctx = cairo.Context(surface)
    ctx.set_source_rgba(1, 1, 1, 1)
    ctx.rectangle(0, 0, width, height)
    ctx.fill()

    return surface

def show_surface(surface):
    width = surface.get_width()
    height = surface.get_height()

    pygame.init()
    pygame.display.set_mode((width, height))

    screen = pygame.display.get_surface()

    while True:
        buf = surface.get_data()
        # TODO: color management is a little funny, probably due to pixel
        # formats here. In a bunch of places we need to call rgb functions
        # but pass things in in g, b, r order.
        image = pygame.image.frombuffer(buf, (width, height), "RGBA")
        # Tranfer to Screen
        screen.blit(image, (0, 0))
        pygame.display.flip()

        process_events(pygame.event.get())
