# XXX: this file will be the abstraction layer between z3 and the rest of the project

import z3

class Context(object):
    def __init__(self):
        self.solver = z3.Solver()

    def add(self, constraint):
        if constraint is not None:
            self.solver.add(constraint)

    # This clears variables and constraints, would be nice if we could choose
    def clear(self):
        self.solver = z3.Solver()

global_ctx = Context()

def clear_context(ctx=global_ctx):
    ctx.clear()

class Var(object):
    def __init__(self, name, ctx=global_ctx):
        self.name = name
        self.var = None

class IntVar(Var):
    def __init__(self, name, ctx=global_ctx):
        super().__init__(name, ctx)
        self.var = z3.Int(name)

class IntRangeVar(IntVar):
    def __init__(self, name=None, ctx=global_ctx, *, min, max):
        super().__init__(name, ctx)
        ctx.solver.add(self.var >= min)
        ctx.solver.add(self.var <= max)

def ASSERT(constraint, ctx=global_ctx):
    ctx.add(constraint)

# XXX operators = ["Distinct", "And", "Or"]

def DISTINCT(l, ctx=global_ctx):
    ctx.add(z3.Distinct([v.var for v in l]))

last_model = None

# XXX this stuff all needs to be reworked
def solvable(ctx=global_ctx):
    return ctx.solver.check() == z3.sat

def next_model(ctx=global_ctx):
    global last_model
    if last_model is not None:
        ctx.solver.add(z3.Or([var() != last_model[var] for var in last_model]))

def get_model(ctx=global_ctx):
    global last_model
    if not solvable(ctx):
        return None
    last_model = ctx.solver.model()
    return last_model

if __name__ == "__main__":
    # test
    print(IntRangeVar("hello", min=1, max=3))
