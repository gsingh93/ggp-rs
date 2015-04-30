use std::collections::{HashMap};
use std::collections::hash_map::Entry::{Occupied, Vacant};

use gdl::{Sentence, Variable, Constant, Rule};

use gdl_parser::visitor::{self, Visitor};

/// Generates new variable names of the form `?R0`, `?R1`, etc.
pub struct VarRenamer {
    id: u32
}

impl VarRenamer {
    pub fn new() -> VarRenamer {
        VarRenamer { id: 0 }
    }

    pub fn rename_rule(&mut self, r: &Rule) -> Rule {
        let mut r = r.clone();
        let mut v = RenamingVisitor::new(self);
        visitor::visit_rule(&mut r, &mut v);
        r
    }

    pub fn rename_sentence(&mut self, s: &Sentence) -> Sentence {
        let mut s = s.clone();
        let mut v = RenamingVisitor::new(self);
        visitor::visit_sentence(&mut s, &mut v);
        s
    }

    fn next_var_name(&mut self) -> String {
        let s = format!("R{}", self.id);
        self.id += 1;
        s
    }
}

/// A `Visitor` that replaces any variables it visits with a new variable name using a `VarRenamer`
struct RenamingVisitor<'a> {
    renamer: &'a mut VarRenamer,
    mapping: HashMap<Constant, Constant>
}

impl<'a> RenamingVisitor<'a> {
    fn new(renamer: &'a mut VarRenamer) -> RenamingVisitor {
        RenamingVisitor { renamer: renamer, mapping: HashMap::new() }
    }
}

impl<'a> Visitor for RenamingVisitor<'a> {
    fn visit_variable(&mut self, var: &mut Variable) {
        let entry = self.mapping.entry(var.name.clone());
        var.name = match entry {
            Occupied(e) => (*e.get()).clone(),
            Vacant(e) => (*e.insert(Constant::new(self.renamer.next_var_name()))).clone()
        };
    }
}
