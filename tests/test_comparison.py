######################################################################
# This file is part of veerer.
#
#       Copyright (C) 2024 Vincent Delecroix
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
import pytest
from veerer import VeeringTriangulation, VeeringTriangulationLinearFamily

def test_comparison():
    vt0 = VeeringTriangulation("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,~8)", "RRBBRRRRB")
    vt1 = VeeringTriangulation("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,~8)", "BRBBRBBRR")
    vt2 = VeeringTriangulation("(0:1)(~0:1,1:1,2:1)(~1:1,~2:1,3:1)(~3:1)", "RRBR")
    vt3 = VeeringTriangulation("(0:1)(~0:1,1:1,2:1)(~1:1,~2:1,3:1)(~3:1)", "BRRB")

    sample = [vt0, vt1, vt2, vt3]
    for i in range(4):
        for j in range(4):
            assert (sample[i] == sample[j]) == (i == j)
            assert (sample[i] != sample[j]) == (i != j)

    f0 = vt0.as_linear_family()
    f1 = vt1.as_linear_family()
    sample = [f0, f1]
    for i in range(2):
        for j in range(2):
            assert (sample[i] == sample[j]) == (i == j)
            assert (sample[i] != sample[j]) == (i != j)

    assert vt0 == f0 and f0 == vt0
    assert vt1 == f1 and f1 == vt1
    assert f0 != vt1 and vt1 != f0
    assert vt0 != f1 and f1 != vt0

    f2 = VeeringTriangulationLinearFamily("(0:1)(~0:1,1:1,2:1)(~1:1,~2:1,3:1)(~3:1)", "RRBR", [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 0)])
    f3 = VeeringTriangulationLinearFamily("(0:1)(~0:1,1:1,2:1)(~1:1,~2:1,3:1)(~3:1)", "BRRB", [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 0)])

    assert vt2 != f2 and f2 != vt2
    assert vt3 != f3 and f3 != vt3
    assert vt2.as_linear_family() != f2

    sample = [vt0, vt1, vt2, vt3]
    for a in sample:
        for b in sample:
            assert (a < b) != (a >= b)
            assert (a > b) != (a <= b)
            assert (a < b) + (a == b) + (a > b) == 1

    sample = [f0, f1, f2, f3, vt2.as_linear_family(), vt3.as_linear_family()]
    for a in sample:
        for b in sample:
            assert (a < b) != (a >= b)
            assert (a > b) != (a <= b)
            assert (a < b) + (a == b) + (a > b) == 1

if __name__ == '__main__':
    import sys
    sys.exit(pytest.main(sys.argv))
