######################################################################
# This file is part of veerer.
#
#       Copyright (C) 2020 Vincent Delecroix
#
# veerer is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# veerer is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with veerer. If not, see <https://www.gnu.org/licenses/>.
######################################################################

import sys
import pytest

import random
from veerer import VeeringTriangulation, RED, BLUE, PURPLE, GREEN

@pytest.mark.parametrize("fp, cols",
[
 ("(0,1,2)", "RRB"),
 ("(0,1,2)", "BBR"),
 ("(0,1,2)", "PBR"),
 ("(0,1,2)", "GRB"),
 ("(0,1,2)", "RPG"),
 ("(0,1,2)", "BGP")
])
def test_triangle(fp, cols):
    V = VeeringTriangulation(fp, cols)
    assert V.angles() == [1, 1, 1, 1], V

@pytest.mark.parametrize("fp, cols",
[
 ("(0,1,2)(~0,~1,~2)", "RRB"),
 ("(0,1,2)(~0,~1,~2)", "BBR"),
 ("(0,1,2)(~0,~1,~2)", "PBR"),
 ("(0,1,2)(~0,~1,~2)", "GRB"),
 ("(0,1,2)(~0,~1,~2)", "RPG"),
 ("(0,1,2)(~0,~1,~2)", "BGP")
])
def test_torus(fp, cols):
    V = VeeringTriangulation(fp, cols)
    assert V.angles() == [2], V

if __name__ == '__main__': sys.exit(pytest.main(sys.argv))
