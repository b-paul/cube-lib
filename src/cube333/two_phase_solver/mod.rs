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

struct Phase1;
struct Phase2;

trait Phase {
    type Cube: PhaseCube;
    type Move: SubMove;
    type Prune: PhasePrune;

    fn get_cube(sym_tables: &SymTables, cube: &CubieCube) -> Self::Cube;

    fn make_move(mover: &Mover, cube: Self::Cube, m: Self::Move) -> Self::Cube;

    fn init_prune(pruner: &Pruner, c: Self::Cube) -> Self::Prune;

    fn update_prune(pruner: &Pruner, p: Self::Prune, c: Self::Cube) -> Self::Prune;
}

impl Phase for Phase1 {
    type Cube = P1Cube;
    type Move = Move333;
    type Prune = P1PruneState;

    fn get_cube(sym_tables: &SymTables, c: &CubieCube) -> P1Cube {
        P1Cube {
            co: sym_tables.co.puzzle_to_sym(c),
            eo: sym_tables.eo.puzzle_to_sym(c),
            slice: coords::ESliceEdgeCoord::from_puzzle(c),
        }
    }

    fn make_move(mover: &Mover, cube: P1Cube, m: Move333) -> P1Cube {
        P1Cube {
            co: mover.p1_co.make_move(cube.co, m),
            eo: mover.p1_eo.make_move(cube.eo, m),
            slice: mover.p1_slice.make_move(cube.slice, m),
        }
    }

    fn init_prune(pruner: &Pruner, c: P1Cube) -> P1PruneState {
        P1PruneState {
            co_slice: pruner.p1_co.bound(c.co, c.slice),
            eo_slice: pruner.p1_eo.bound(c.eo, c.slice),
        }
    }

    fn update_prune(pruner: &Pruner, p: P1PruneState, c: P1Cube) -> P1PruneState {
        P1PruneState {
            co_slice: pruner.p1_co.update(p.co_slice, c.co, c.slice),
            eo_slice: pruner.p1_eo.update(p.eo_slice, c.eo, c.slice),
        }
    }
}

impl Phase for Phase2 {
    type Cube = P2Cube;
    type Move = DrMove;
    type Prune = P2PruneState;

    fn get_cube(sym_tables: &SymTables, c: &CubieCube) -> P2Cube {
        P2Cube {
            cp: sym_tables.cp.puzzle_to_sym(c),
            ep: sym_tables.ep.puzzle_to_sym(c),
            slice: coords::DominoESliceCoord::from_puzzle(c),
        }
    }

    fn make_move(mover: &Mover, cube: P2Cube, m: DrMove) -> P2Cube {
        P2Cube {
            cp: mover.p2_cp.make_move(cube.cp, m),
            ep: mover.p2_ep.make_move(cube.ep, m),
            slice: mover.p2_slice.make_move(cube.slice, m),
        }
    }

    fn init_prune(pruner: &Pruner, c: P2Cube) -> P2PruneState {
        P2PruneState {
            cp_slice: pruner.p2_cp.bound(c.cp, c.slice),
            ep_slice: pruner.p2_ep.bound(c.ep, c.slice),
        }
    }

    fn update_prune(pruner: &Pruner, p: P2PruneState, c: P2Cube) -> P2PruneState {
        P2PruneState {
            cp_slice: pruner.p2_cp.update(p.cp_slice, c.cp, c.slice),
            ep_slice: pruner.p2_ep.update(p.ep_slice, c.ep, c.slice),
        }
    }
}

trait PhaseCube: Copy {
    fn is_solved(self) -> bool;
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

impl PhaseCube for P1Cube {
    fn is_solved(self) -> bool {
        // TODO this sucks
        self.co.class() == 0 && self.eo.class() == 0 && self.slice.repr() == 0
    }
}

impl PhaseCube for P2Cube {
    fn is_solved(self) -> bool {
        self.cp.class() == 0 && self.ep.class() == 0 && self.slice.repr() == 0
    }
}

trait PhasePrune: Copy {
    fn val(self) -> usize;
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

impl PhasePrune for P1PruneState {
    fn val(self) -> usize {
        self.co_slice.max(self.eo_slice)
    }
}

impl PhasePrune for P2PruneState {
    fn val(self) -> usize {
        self.cp_slice.max(self.ep_slice)
    }
}

struct Mover {
    p1_co: Rc<move_tables::COSymMoveTable>,
    p1_eo: Rc<move_tables::EOSymMoveTable>,
    p1_slice: Rc<move_tables::ESliceEdgeMoveTable>,
    p2_cp: Rc<move_tables::DominoCPSymMoveTable>,
    p2_ep: Rc<move_tables::DominoEPSymMoveTable>,
    p2_slice: Rc<move_tables::DominoESliceMoveTable>,
}

struct Pruner {
    p1_co: prune::ESliceTwistPruneTable,
    p1_eo: prune::ESliceFlipPruneTable,
    p2_cp: prune::DominoSliceCPPruneTable,
    p2_ep: prune::DominoSliceEPPruneTable,
}

struct SymTables {
    co: Rc<coords::RawSymTable<coords::COSymCoord>>,
    eo: Rc<coords::RawSymTable<coords::EOSymCoord>>,
    cp: Rc<coords::RawSymTable<coords::CPSymCoord>>,
    ep: Rc<coords::RawSymTable<coords::DominoEPSymCoord>>,
}

impl SymTables {

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
        let p1 = self.solve_phase::<Phase1>(&cube);
        let cube = cube.make_moves(MoveSequence(p1.clone()));
        let mut p2 = self.solve_phase::<Phase2>(&cube);

        let mut sol = p1;
        sol.append(&mut p2);
        MoveSequence(sol).cancel()
    }

    fn solve_phase<P: Phase>(&self, cube: &CubieCube) -> Vec<Move333> {
        let cube = P::get_cube(&self.sym_tables, cube);
        let prune = P::init_prune(&self.pruner, cube);
        let mut sol = Vec::new();

        let mut depth = 0;
        while depth < 20 {
            depth = self.search_phase::<P>(cube, prune, &mut sol, 0, depth);
            if depth == 50 {
                return sol.into_iter().map(|m| m.into_move()).collect();
            }
        }

        panic!("No phase 2 solution found in 20 moves")
    }

    fn search_phase<P: Phase>(
        &self,
        cube: P::Cube,
        prune: P::Prune,
        sol: &mut Vec<P::Move>,
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
        for &m in P::Move::MOVE_LIST {
            // TODO eliminate redundant moves
            let cube2 = P::make_move(&self.mover, cube, m);
            let prune2 = P::update_prune(&self.pruner, prune, cube2);
            sol.push(m);

            let depth = self.search_phase::<P>(cube2, prune2, sol, cost + 1, depth);
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
