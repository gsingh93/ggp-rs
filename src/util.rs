use gdl::{Move, Role, Relation, Constant, Sentence};

pub fn cross_product<T: Clone>(v: Vec<Vec<T>>) -> Vec<Vec<T>> {
    fn helper<'a, T: Clone>(v: &'a [Vec<T>], res: &mut Vec<Vec<T>>, partial: &mut Vec<&'a T>) {
        if v.len() == partial.len() {
            res.push(partial.iter().map(|x| (**x).clone()).collect());
        } else {
            assert!(partial.len() < v.len());
            for t in v[partial.len()].iter() {
                partial.push(t);
                helper(v, res, partial);
                partial.pop().unwrap();
            }
        }
    }

    let mut res = Vec::new();
    helper(&*v, &mut res, &mut Vec::new());
    res
}

pub fn create_does(r: &Role, m: &Move) -> Sentence {
    Relation::new("does", vec![Constant::new(r.name()).into(), m.contents.clone()]).into()
}
