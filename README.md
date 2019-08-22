Solvers for various kinds of puzzles, using z3. Many of them even work :)

This is not at all very tidy right now; this is more a work-in-progress to
think of what a library built around z3 to make it easy to write solvers
would look like.

This only works in python3.

To get going:

apt install python3 python3-pip python3-venv pkg-config libcairo2-dev  # or whatever, good luck

pip install virtualenv  # or maybe pip3
virtualenv venv  # or maybe virtualenv -p python3 venv... or whatever, good luck
. venv/bin/activate  # do just this line each time you come back to the project
pip install -r requirements.txt  # or maybe pip3

Note that this will install the correct package "z3-solver", NOT the totally
  unrelated and unhelpful package named "z3".

Now try it out:

python slitherlink.py  # or maybe python3

After a moment, you should get a popup with a rendered picture of a solved
  slitherlink.
