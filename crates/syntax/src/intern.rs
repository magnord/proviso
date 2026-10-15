//! Interned names, so the tree compares and stores identifiers as integers.

use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Symbol(u32);

#[derive(Default)]
pub struct Interner {
    map: HashMap<Box<str>, Symbol>,
    names: Vec<Box<str>>,
}

impl Interner {
    pub fn intern(&mut self, name: &str) -> Symbol {
        if let Some(sym) = self.map.get(name).copied() {
            return sym;
        }
        let sym = Symbol(u32::try_from(self.names.len()).expect("more than u32::MAX names"));
        self.names.push(name.into());
        self.map.insert(name.into(), sym);
        sym
    }

    pub fn lookup(&self, name: &str) -> Option<Symbol> {
        self.map.get(name).copied()
    }

    pub fn resolve(&self, sym: Symbol) -> &str {
        &self.names[sym.0 as usize]
    }
}
