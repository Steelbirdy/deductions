use tests::sympy::{Fact, knowledge_base};

fn main() {
    let kb = knowledge_base();
    println!("Commutative = {:?}", kb.get(Fact::Commutative).unwrap_or_default());
}