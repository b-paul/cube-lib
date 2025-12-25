//! An implementation of the two phase solver described [here](https://kociemba.org/cube.htm).

mod coords;
mod move_tables;
mod prune;
mod symmetry;

use coords::SymCoordinate;
use move_tables::{DrMove, SubMove};

use super::{CubieCube, moves::Move333};
use crate::coord::Coordinate;
use crate::moves::MoveSequence;

use std::rc::Rc;

struct Mover {
    p1_co: Rc<move_tables::COSymMoveTable>,
    p1_eo: Rc<move_tables::EOSymMoveTable>,
    p1_slice: Rc<move_tables::ESliceEdgeMoveTable>,
    p2_cp: Rc<move_tables::DominoCPSymMoveTable>,
    p2_ep: Rc<move_tables::DominoEPSymMoveTable>,
    p2_slice: Rc<move_tables::DominoESliceMoveTable>,
}

impl Mover {
    fn make_p1_move(&self, cube: P1Cube, m: Move333) -> P1Cube {
        let co = self.p1_co.make_move(cube.co, m);
        let eo = self.p1_eo.make_move(cube.eo, m);
        let slice = self.p1_slice.make_move(cube.slice, m);
        P1Cube { co, eo, slice }
    }

    fn make_p2_move(&self, cube: P2Cube, m: DrMove) -> P2Cube {
        let cp = self.p2_cp.make_move(cube.cp, m);
        let ep = self.p2_ep.make_move(cube.ep, m);
        let slice = self.p2_slice.make_move(cube.slice, m);
        P2Cube { cp, ep, slice }
    }
}

struct Pruner {
    p1_co: prune::ESliceTwistPruneTable,
    p1_eo: prune::ESliceFlipPruneTable,
    p2_cp: prune::DominoSliceCPPruneTable,
    p2_ep: prune::DominoSliceEPPruneTable,
}

impl Pruner {
    fn init_prune_p1(&self, c: P1Cube) -> P1PruneState {
        P1PruneState {
            co_slice: self.p1_co.bound(c.co, c.slice),
            eo_slice: self.p1_eo.bound(c.eo, c.slice),
        }
    }

    fn update_prune_p1(&self, p: P1PruneState, c: P1Cube) -> P1PruneState {
        let co_slice = self.p1_co.update(p.co_slice, c.co, c.slice);
        let eo_slice = self.p1_eo.update(p.eo_slice, c.eo, c.slice);
        P1PruneState { co_slice, eo_slice }
    }

    fn init_prune_p2(&self, c: P2Cube) -> P2PruneState {
        P2PruneState {
            cp_slice: self.p2_cp.bound(c.cp, c.slice),
            ep_slice: self.p2_ep.bound(c.ep, c.slice),
        }
    }

    fn update_prune_p2(&self, p: P2PruneState, c: P2Cube) -> P2PruneState {
        let cp_slice = self.p2_cp.update(p.cp_slice, c.cp, c.slice);
        let ep_slice = self.p2_ep.update(p.ep_slice, c.ep, c.slice);
        P2PruneState { cp_slice, ep_slice }
    }
}

struct SymTables {
    co: Rc<coords::RawSymTable<coords::COSymCoord>>,
    eo: Rc<coords::RawSymTable<coords::EOSymCoord>>,
    cp: Rc<coords::RawSymTable<coords::CPSymCoord>>,
    ep: Rc<coords::RawSymTable<coords::DominoEPSymCoord>>,
}

impl SymTables {
    fn get_p1_cube(&self, c: &CubieCube) -> P1Cube {
        P1Cube {
            co: self.co.puzzle_to_sym(c),
            eo: self.eo.puzzle_to_sym(c),
            slice: coords::ESliceEdgeCoord::from_puzzle(c),
        }
    }

    fn get_p2_cube(&self, c: &CubieCube) -> P2Cube {
        P2Cube {
            cp: self.cp.puzzle_to_sym(c),
            ep: self.ep.puzzle_to_sym(c),
            slice: coords::DominoESliceCoord::from_puzzle(c),
        }
    }
}

#[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash)]
struct P1PruneState {
    co_slice: usize,
    eo_slice: usize,
}

#[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash)]
struct P2PruneState {
    cp_slice: usize,
    ep_slice: usize,
}

impl P1PruneState {
    fn val(self) -> usize {
        self.co_slice.max(self.eo_slice)
    }
}

impl P2PruneState {
    fn val(self) -> usize {
        self.cp_slice.max(self.ep_slice)
    }
}

#[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash)]
struct P1Cube {
    co: coords::COSymCoord,
    eo: coords::EOSymCoord,
    slice: coords::ESliceEdgeCoord,
}

#[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash)]
struct P2Cube {
    cp: coords::CPSymCoord,
    ep: coords::DominoEPSymCoord,
    slice: coords::DominoESliceCoord,
}

impl P1Cube {
    fn is_solved(self) -> bool {
        // TODO this sucks
        self.co.class() == 0 && self.eo.class() == 0 && self.slice.repr() == 0
    }
}

impl P2Cube {
    fn is_solved(self) -> bool {
        self.cp.class() == 0 && self.ep.class() == 0 && self.slice.repr() == 0
    }
}

/// A cube solver that uses Kociemba's two phase algorithm.
pub struct Solver {
    mover: Mover,
    pruner: Pruner,
    sym_tables: SymTables,
}

impl Default for Solver {
    fn default() -> Self {
        Self::new()
    }
}

impl Solver {
    /// Create a solver.
    pub fn new() -> Self {
        // this is so ugly...
        let co_sym = Rc::new(coords::RawSymTable::generate());
        let eo_sym = Rc::new(coords::RawSymTable::generate());
        let cp_sym = Rc::new(coords::RawSymTable::generate());
        let ep_sym = Rc::new(coords::RawSymTable::generate());
        let p1_co = Rc::new(move_tables::SymMoveTable::generate(&co_sym));
        let p1_eo = Rc::new(move_tables::SymMoveTable::generate(&eo_sym));
        let p1_slice = Rc::new(move_tables::MoveTable::generate());
        let p2_cp = Rc::new(move_tables::SymMoveTable::generate(&cp_sym));
        let p2_ep = Rc::new(move_tables::SymMoveTable::generate(&ep_sym));
        let p2_slice = Rc::new(move_tables::MoveTable::generate());

        let mover = Mover {
            p1_co,
            p1_eo,
            p1_slice,
            p2_cp,
            p2_ep,
            p2_slice,
        };

        let p1_co = prune::SymRawPruningTable::generate(
            co_sym.clone(),
            mover.p1_co.clone(),
            mover.p1_slice.clone(),
        );
        let p1_eo = prune::SymRawPruningTable::generate(
            eo_sym.clone(),
            mover.p1_eo.clone(),
            mover.p1_slice.clone(),
        );
        let p2_cp = prune::SymRawPruningTable::generate(
            cp_sym.clone(),
            mover.p2_cp.clone(),
            mover.p2_slice.clone(),
        );
        let p2_ep = prune::SymRawPruningTable::generate(
            ep_sym.clone(),
            mover.p2_ep.clone(),
            mover.p2_slice.clone(),
        );

        let pruner = Pruner {
            p1_co,
            p1_eo,
            p2_cp,
            p2_ep,
        };

        let sym_tables = SymTables {
            co: co_sym,
            eo: eo_sym,
            cp: cp_sym,
            ep: ep_sym,
        };

        Self {
            mover,
            pruner,
            sym_tables,
        }
    }

    /// Obtain a solving sequence for the cube (such that applying the sequence solves the cube).
    pub fn solve(&self, cube: CubieCube) -> MoveSequence<Move333> {
        let p1 = self.solve_p1(&cube);
        let cube = cube.make_moves(MoveSequence(p1.clone()));
        let mut p2 = self.solve_p2(&cube);

        let mut sol = p1;
        sol.append(&mut p2);
        MoveSequence(sol).cancel()
    }

    fn solve_p1(&self, cube: &CubieCube) -> Vec<Move333> {
        let cube = self.sym_tables.get_p1_cube(cube);
        let prune = self.pruner.init_prune_p1(cube);
        let mut sol = Vec::new();

        let mut depth = 0;
        while depth < 20 {
            depth = self.search_p1(cube, prune, &mut sol, 0, depth);
            if depth == 50 {
                return sol;
            }
        }

        panic!("No phase 1 solution found in 20 moves")
    }

    fn search_p1(
        &self,
        cube: P1Cube,
        prune: P1PruneState,
        sol: &mut Vec<Move333>,
        cost: usize,
        depth: usize,
    ) -> usize {
        if cube.is_solved() {
            // TODO why 50...
            return 50;
        }
        let estimate = cost + prune.val();
        if estimate > depth {
            return estimate;
        }
        let mut min = usize::MAX;
        for &m in Move333::MOVE_LIST {
            // TODO eliminate redundant moves
            let cube2 = self.mover.make_p1_move(cube, m);
            let prune2 = self.pruner.update_prune_p1(prune, cube2);
            sol.push(m);

            let depth = self.search_p1(cube2, prune2, sol, cost + 1, depth);
            if depth == 50 {
                return 50;
            }
            min = min.min(depth);

            sol.pop();
        }

        min
    }

    // WHY IS IT COPY PASTED AAAAAAAAA
    fn solve_p2(&self, cube: &CubieCube) -> Vec<Move333> {
        let cube = self.sym_tables.get_p2_cube(cube);
        let prune = self.pruner.init_prune_p2(cube);
        let mut sol = Vec::new();

        let mut depth = 0;
        while depth < 20 {
            depth = self.search_p2(cube, prune, &mut sol, 0, depth);
            if depth == 50 {
                return sol.into_iter().map(|m| m.into_move()).collect();
            }
        }

        panic!("No phase 2 solution found in 20 moves")
    }

    fn search_p2(
        &self,
        cube: P2Cube,
        prune: P2PruneState,
        sol: &mut Vec<DrMove>,
        cost: usize,
        depth: usize,
    ) -> usize {
        if cube.is_solved() {
            // TODO why 50...
            return 50;
        }
        let estimate = cost + prune.val();
        if estimate > depth {
            return estimate;
        }
        let mut min = usize::MAX;
        for &m in DrMove::MOVE_LIST {
            // TODO eliminate redundant moves
            let cube2 = self.mover.make_p2_move(cube, m);
            let prune2 = self.pruner.update_prune_p2(prune, cube2);
            sol.push(m);

            let depth = self.search_p2(cube2, prune2, sol, cost + 1, depth);
            if depth == 50 {
                return 50;
            }
            min = min.min(depth);

            sol.pop();
        }

        min
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use proptest::collection::vec;
    use proptest::prelude::*;

    #[test]
    fn solve() {
        let solver = Solver::new();
        proptest!(|(mvs in vec(any::<Move333>(), 0..20).prop_map(MoveSequence))| {
            let cube = CubieCube::SOLVED.make_moves(mvs.clone());
            let sol = solver.solve(cube.clone());
            assert_eq!(cube.make_moves(sol), CubieCube::SOLVED);
        });
    }
}
