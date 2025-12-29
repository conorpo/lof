#![allow(non_snake_case)]
#![feature(box_patterns)]
use core::panic;
use std::{ collections::VecDeque, fmt::{self, Write}, rc::Rc};



// All terms are part of base syntax
// But some terms are only checkable for types, not inferrable
// These terms also sometimes need inferrable subterms
// In this file we could technically wrap any term in Inf, but outside we would only be able to use the constructors mod.

#[derive(Clone)]
enum TermInf {
    U(usize),
    //Ann(T, T),
    Var(usize),
    App(Box<TermInf>, Box<TermChk>),
    Pi(Box<TermChk>, Box<Binder>),
    Sig(Box<TermChk>, Box<Binder>),
    
}

// Terms that can be type checked
#[derive(Clone)]
enum TermChk {
    Inf(TermInf), // All inferrable terms
    Lam(Box<Binder>),
    Pair(Box<TermChk>, Box<TermChk>),
}

#[derive(Clone)]
struct Binder(TermChk);
impl From<TermChk> for Binder {
    fn from(value: TermChk) -> Self {
        Binder(value)
    }
}


impl Binder {
    // fn infer_type(&self, context: &mut Context, binding_type: &Term) -> Term {
    //     context.0.push_front(binding_type.clone());
    //     let res = self.0.infer_type(context);
    //     context.0.pop_front();
    //     res
    // }

    // todo, change to create new Term for now
    fn substitute(&self, idx: usize, val: &TermInf) -> Binder {
        Binder(self.0.substitute(idx + 1, val))
    }

    fn has_type(&self, t: &TermChk, context: &mut Context, binding_type: &TermInf) -> bool {
        context.0.push_front(binding_type.clone());
        let res = self.0.has_type(t, context);
        context.0.pop_front();
        res
    }
}


impl fmt::Debug for TermInf {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut variable_names = VecDeque::new();
        variable_names.extend(vars[0..3].iter());
        self.debug_helper(f, &mut variable_names)
    }
}

const vars: [char; 25] = ['A','B','C', 'a','b','c','d','e','i','j','k','l','m','n','o','p','q','r','s','t','u','v','w','α','β'];

struct Context(VecDeque<TermInf>);

// Notes: Am I really using the context correctly?
impl TermInf {
    fn infer_type(&self, context: &mut Context) -> TermInf {
        use TermInf::*;
        match self {
            App(box f, box x) => {
                let t_f = f.infer_type(context).normalize();
                let Pi(box dom, box type_family) = t_f else { panic!("Cannot apply non-function.") };
                
                if x.has_type(&dom, context) {
                    let mut body = type_family.clone(); //todo, wont be needed when sub clones
                    body.substitute(0, &x.normalize());
                    body.normalize()
                } else {
                    panic!("Function domain does not match argument type.")
                }
            },
            &Var(idx) => {
                context.0[idx].clone()
            },
            U(idx) => {
                U(idx +  1)
            },
            Pi(box index, box type_family) | Sig(box index, box type_family) => {
                // Todo, with one universe we would be able to check these having to infer, might have to make a seperate func
                if !index.has_type(&TermChk::Inf(U(0)), context)  { panic!("Type Family is not being indexed from a type.") };
                let index = index.normalize();
                if !type_family.has_type(&U(0), context, &index)  { panic!("Type Family is not being indexed from a type.") };

                U(0)
            },
            _ => panic!("These terms are never inferrable.")
        }
    }


    fn debug_helper(&self, f: &mut fmt::Formatter<'_>, variable_names: &mut VecDeque<char>) -> fmt::Result {
        use TermInf::*;
        match self {
            Var(idx) => {  f.write_fmt(format_args!("{}", variable_names[*idx])) },
            TermInf::Pi(dom, Binder(type_family)) => { 
                let new_var = vars[variable_names.len()];
                f.write_fmt(format_args!("\\prod_{{{new_var}:"))?;
                dom.debug_helper(f, variable_names)?;
                f.write_str("} ")?;
                variable_names.push_front(new_var);
                type_family.debug_helper(f, variable_names)
            },
            TermInf::Lam(Binder(body)) => {
                let new_var = vars[variable_names.len()];
                f.write_fmt(format_args!("(\\: λ_{{{new_var}"))?;
                variable_names.push_front(new_var);
                body.debug_helper(f, variable_names)?;
                f.write_str("\\:)")
            },
            TermInf::App(Inf(g), x) => {
                g.debug_helper(f, variable_names)?;
                f.write_char(' ')?;
                x.debug_helper(f, variable_names)
            },
            TermInf::Pair(a, b) => {
                f.write_char('(')?;
                a.debug_helper(f, variable_names)?;
                f.write_char(',')?;
                b.debug_helper(f, variable_names)?;
                f.write_char(')')
            },
            TermInf::Sig(index, Binder(type_family)) => {
                let new_var = vars[variable_names.len()];
                f.write_fmt(format_args!("\\sum_{{{new_var}:"))?;
                index.debug_helper(f, variable_names);
                f.write_str("} ")?;
                variable_names.push_front(new_var);
                type_family.debug_helper(f, variable_names)
            },
            TermInf::U(usize) => {
                f.write_fmt(format_args!("\\mathcal{{U}}_{usize}"))
            }
            _ => { unimplemented!() }
        }
    }


    fn substitute(&self, idx: usize, val: &TermInf) -> TermInf {
        use TermInf::*;
        match self {
            &Var(vidx) if vidx == idx => {
                val.clone()
            },
            App(box a, box b) => {
                App(
                    Box::new(a.substitute(idx, val)),
                    Box::new(b.substitute(idx, val))
                )
            },
            Pi(box index, box type_family) => {
                Pi(
                    Box::new(index.substitute(idx, val)),
                    Box::new(type_family.substitute(idx, val))
                )
            },
            Sig(box index, box type_family) => {
                Sig(
                    Box::new(index.substitute(idx, val)),
                    Box::new(type_family.substitute(idx, val))
                )
            },
            other => other.clone(),
        }
    }


    fn normalize(&self) -> TermInf {
        self.clone()
    }

    fn is_universe(&self) -> bool {
        match self {
            TermInf::U(_) => true,
            _ => false
        }
    }

    fn is_type_former(&self) -> bool {
        use TermInf::*;
        match self {
            &Sig(_,_) => true,
            &Pi(_,_) => true,
            _ => false
        }
    }

    fn is_judgementally_equal(&self, other: &TermInf) -> bool {
        // match (self, other) {
        //     (&U(i), &U(i2)) | (&Var(i), &Var(i2)) => i == i2,
        //     (Func(dom, cod), Func(dom2, cod2)) 
        //   | (DepFunc(Abs(dom,cod)), DepFunc(Abs(dom2, cod2))) 
        //   | (DepPair(Abs(dom,cod)), DepPair(Abs(dom2, cod2))) => {
        //         dom.is_judgementally_equal(dom2) && cod.is_judgementally_equal(cod2)
        //     },
        //     _ => panic!()


        // }
        todo!("Judgemental Equality")
    }
}

impl TermChk {
    fn has_type(&self, t: &Self, context: &mut Context) -> bool {
        match self {
            TermChk::Inf(inferrable) => {
                inferrable.infer_type(context).is_judgementally_equal(t)
            },
            TermChk::Lam(body) => {
                let TermChk::Inf(box TermInf::Pi(dom, type_family)) = t else { panic!("Lamba can only be checked against a Pi type.") };
                let dom = &dom.normalize();
                body.has_type(&type_family.0, context, dom)
            },
            Pair(a,b) => {
                let Sig(index, type_family) = t else { panic!("Pair can only be checked against a Sig type.")};
                let index = index.normalize();
                if !a.has_type(&index, context) { panic!("First element in pair does not match index of Sig."); }  
                let mut b_type = type_family.0.clone(); //todo, wont be needed when sub clones
                b_type.substitute(0, a);
                b.has_type(&b_type, context)
            },
            other => {
                Inf(Box::new(other)).infer_type(context).is_judgementally_equal(t)
            }
        }
    }

    fn substitute(&self, index: usize, val: &TermInf) -> TermChk {
        use TermChk::*;
        match self {
            Lam(box body) => {
                Lam(Box::new(body.substitute(index, val)))
            },
            Pair(box a, box b) => {
                Pair(
                    Box::new(a.substitute(index, val)), 
                    Box::new(b.substitute(index, val))    
                )
            },
            Inf(inf) => {
                Inf(inf.substitute(index, val))
            }
        }
    }
}

// For simple test writing while I don't have a surface syntax, 
// really should be a job for macros but at that point it's
// probably worth it to create a parser / interpreter
mod constructors {
    use super::*;

    pub fn U(idx: usize) -> Inf {
        Inf(Box::new(TermInf::U(idx)))
    }

    pub fn Var(idx: usize) -> Inf {
        Inf(Box::new(TermInf::Var(idx)))
    }

    pub fn App(a: Inf, b: impl Into<Box<TermInf>>) -> Inf {
        Inf(Box::new(TermInf::App(a, b.into())))
    }
    
    pub fn Pi(a: impl Into<Box<TermInf>>, b: impl Into<Binder>) -> Inf {
        Inf(Box::new(TermInf::Pi(a.into(), b.into())))
    }

    pub fn Sig(a: impl Into<Box<TermInf>>, b: impl Into<Binder>) -> Inf {
        Inf(Box::new(TermInf::Sig(a.into(), b.into())))
    }

    pub fn Lam(body: impl Into<Binder>) -> Box<TermInf> {
        Box::new(TermInf::Lam(body.into()))
    }

    pub fn Pair<T : Into<Box<TermInf>>>(a: T, b: T) -> Box<TermInf> {
        Box::new(TermInf::Pair(a.into(),b.into()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use constructors::*;
    
    #[test]
    fn debug_some_stuff() {
        let new_type = Pi(U(0), Pi(Var(0), Sig(Var(0), Var(1))));

        println!("$$ {:?} $$", &new_type.0);

        let new_term = Lam(
            Lam(
                Pair(Var(0), Var(0))
            )
        );

        println!("$$ {:?} $$",new_term);

        let mut context = Context(VecDeque::new());
        dbg!(new_term.has_type(&new_type.0, &mut context));

        assert!(true);
    }
}
