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
from veerer import VeeringTriangulation, StrebelGraph, VeeringTriangulationLinearFamily, StrebelGraphLinearFamily

def _check_comparison_consistency(a, b):
    lt = a < b
    le = a <= b
    eq = a == b
    ne = a != b
    gt = a > b
    ge = a >= b

    assert lt == (b > a)
    assert le == (b >= a)
    assert eq == (b == a)
    assert ne == (b != a)
    assert gt == (b < a)
    assert ge == (b <= a)

    assert lt + eq + gt == 1
    assert eq + ne == 1
    assert lt + ge == 1
    assert gt + le == 1
    assert lt + gt == ne
    assert le == lt + eq
    assert ge == gt + eq

def _check_comparison_sample_consistency(sample):
    for a in sample:
        for b in sample:
            _check_comparison_consistency(a, b)


def test_veering_triangulation_comparison():
    vt0 = VeeringTriangulation("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,~8)", "RRBBRRRRB")
    vt1 = VeeringTriangulation("(0,1,2)(~0,~1,3)(~2,4,5)(~3,~4,6)(~5,7,8)(~6,~7,~8)", "BRBBRBBRR")
    vt2 = VeeringTriangulation("(0:1)(~0:1,1:1,2:1)(~1:1,~2:1,3:1)(~3:1)", "RRBR")
    vt3 = VeeringTriangulation("(0:1)(~0:1,1:1,2:1)(~1:1,~2:1,3:1)(~3:1)", "BRRB")

    sample = [vt0, vt1, vt2, vt3]
    fsample = [vt.as_linear_family() for vt in sample]
    for i in range(4):
        for j in range(4):
            assert (sample[i] == sample[j]) == (sample[i] == fsample[j]) == (fsample[i] == sample[j]) == (fsample[i] == fsample[j]) == (i == j)
            assert (sample[i] != sample[j]) == (sample[i] != fsample[j]) == (fsample[i] != sample[j]) == (fsample[i] != fsample[j]) == (i != j)


    f4 = VeeringTriangulationLinearFamily("(0:1)(~0:1,1:1,2:1)(~1:1,~2:1,3:1)(~3:1)", "RRBR", [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 0)])
    f5 = VeeringTriangulationLinearFamily("(0:1)(~0:1,1:1,2:1)(~1:1,~2:1,3:1)(~3:1)", "BRRB", [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 0)])

    _check_comparison_sample_consistency(sample)
    _check_comparison_sample_consistency(fsample + [f4, f5])


def test_strebel_graph_comparison():
    sg0 = StrebelGraph("(0,~0:1)")
    sg1 = StrebelGraph("(0,~0:2)")
    sg2 = StrebelGraph("(0:1,1:0,~1:1,~0:0)")

    sample = [sg0, sg1, sg2]
    fsample = [sg.as_linear_family() for sg in sample]
    for i in range(3):
        for j in range(3):
            assert (sample[i] == sample[j]) == (sample[i] == fsample[j]) == (fsample[i] == sample[j]) == (fsample[i] == fsample[j]) == (i == j)
            assert (sample[i] != sample[j]) == (sample[i] != fsample[j]) == (fsample[i] != sample[j]) == (fsample[i] != fsample[j]) == (i != j)

    _check_comparison_sample_consistency(sample)
    _check_comparison_sample_consistency(fsample)


if __name__ == '__main__':
    import sys
    sys.exit(pytest.main(sys.argv))
