A PPX Rewriter for Simplifying Generated Code

### Version

This is ``pa_ppx_simplify`` (alpha) version 0.01.

# Overview

What it says on the tin.  Initially, only eta-reduction.  Meant to be
used as cleanup after code generation, typically for human consumption
(the assumption is that compilers will do all the simplifying
themselves, but for humans, it might help for debugging to get ride of
all the superfluous redexes (assuming it's done ... *correctly*).
