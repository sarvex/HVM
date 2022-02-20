// Moving Lambolt Terms to/from runtime, and building dynamic functions.
// TODO: "dups" still needs to be moved out on alloc_body etc.

use crate::language as lang;
use crate::readback as rd;
use crate::rulebook as rb;
use crate::runtime as rt;
use std::iter;
use std::time::Instant;
use std::collections::{HashMap};

#[derive(Debug)]
pub enum DynTerm {
  Var { bidx: u64 },
  Glo { name: String },
  Dup { eras: (bool, bool), expr: Box<DynTerm>, body: Box<DynTerm> },
  Let { expr: Box<DynTerm>, body: Box<DynTerm> },
  Lam { eras: bool, glob: Option<String>, body: Box<DynTerm> },
  App { func: Box<DynTerm>, argm: Box<DynTerm> },
  Cal { func: u64, args: Vec<DynTerm> },
  Ctr { func: u64, args: Vec<DynTerm> },
  U32 { numb: u32 },
  Op2 { oper: u64, val0: Box<DynTerm>, val1: Box<DynTerm> },
}

// The right-hand side of a rule, "digested" or "pre-filled" in a way that is almost ready to be
// pasted into the runtime's memory, except for some minor adjustments: internal links need to be
// adjusted taking in account the index where each node is actually allocated, and external
// variables must be linked. This structure helps moving as much computation from the interpreter
// to the static time (i.e., when generating the dynfun closure) as possible.
pub type Body = (Elem, Vec<Node>); // The pre-filled body (TODO: can the Node Vec be unboxed?)
pub type Node = Vec<Elem>; // A node on the pre-filled body
#[derive(Copy, Clone, Debug)]
pub enum Elem {
  // An element of a node
  Fix { value: u64 }, // Fixed value, doesn't require adjustment
  Loc { value: u64, targ: u64, slot: u64 }, // Local link, requires adjustment
  Ext { index: u64 }, // Link to an external variable
}

#[derive(Debug)]
pub struct DynVar {
  pub param: u64,
  pub field: Option<u64>,
  pub erase: bool,
}

#[derive(Debug)]
pub struct DynRule {
  pub cond: Vec<rt::Lnk>,
  pub vars: Vec<DynVar>,
  pub term: DynTerm,
  pub body: Body,
  pub free: Vec<(u64, u64)>,
}

#[derive(Debug)]
pub struct DynFun {
  pub redex: Vec<bool>,
  pub rules: Vec<DynRule>,
}

pub fn build_dynfun(
  comp: &rb::RuleBook,
  rules: &[lang::Rule],
) -> DynFun {
  let mut redex = if let lang::Term::Ctr { name: _, ref args } = *rules[0].lhs {
    vec![false; args.len()]
  } else {
    panic!("Invalid left-hand side: {}", rules[0].lhs);
  };
  let dynrules = rules
    .iter()
    .filter_map(|rule| {
      if let lang::Term::Ctr { ref name, ref args } = *rule.lhs {
        let mut cond = Vec::new();
        let mut vars = Vec::new();
        let mut free = Vec::new();
        if args.len() != redex.len() {
          panic!("Inconsistent length of left-hand side on equation for '{}'.", name);
        }
        for ((i, arg), redex) in args.iter().enumerate().zip(redex.iter_mut()) {
          match &**arg {
            lang::Term::Ctr { name, args } => {
              *redex = true;
              cond.push(rt::Ctr(args.len() as u64, *comp.name_to_id.get(&*name).unwrap_or(&0), 0));
              free.push((i as u64, args.len() as u64));
              for (j, arg) in args.iter().enumerate() {
                if let lang::Term::Var { ref name } = **arg {
                  vars.push(DynVar { param: i as u64, field: Some(j as u64), erase: name == "*" });
                } else {
                  panic!("Sorry, left-hand sides can't have nested constructors yet.");
                }
              }
            }
            lang::Term::U32 { numb } => {
              *redex = true;
              cond.push(rt::U_32(*numb as u64));
            }
            lang::Term::Var { name } => {
              cond.push(0);
              vars.push(DynVar { param: i as u64, field: None, erase: name == "*" });
            }
            _ => {
              panic!("Invalid left-hand side.");
            }
          }
        }

        let term = term_to_dynterm(comp, &rule.rhs, vars.len() as u64);
        let body = build_body(&term, vars.len() as u64);

        Some(DynRule { cond, vars, term, body, free })
      } else {
        None
      }
    })
    .collect();
  DynFun { redex, rules: dynrules }
}

fn get_var(mem: &rt::Worker, term: rt::Lnk, var: &DynVar) -> rt::Lnk {
  let DynVar { param, field, erase: _ } = var;
  match field {
    Some(i) => rt::ask_arg(mem, rt::ask_arg(mem, term, *param), *i),
    None => rt::ask_arg(mem, term, *param),
  }
}

/// This is used to color fan nodes. We need a globally unique color for each
/// generated node. Right now, we just increment this counter every time we
/// generate a node. Node that this is done at compile-time, so, calling the
/// same function will always return the same fan node colors. That is, colors
/// are only globally unique across different functions, not across different
/// function calls.
///
/// We could move this to the runtime, though, which would make Lambolt somewhat
/// more expressive. For example:
///
/// ```not_rust
/// (Two)  = λf λx (f (f x))
/// (Main) = ((Two) (Two))
/// ```
///
/// Isn't admissible in the current runtime, but it would if we generated new
/// fan nodes per each global function call.

//#[derive(Debug)]
//pub struct DupsCount(u64);
//impl DupsCount {
  //fn new() -> Self {
    //Self(0)
  //}
  //fn next(&mut self) -> u64 {
    //let ret = self.0;
    //self.0 += 1;
    //ret
  //}
//}

pub fn build_runtime_functions(comp: &rb::RuleBook) -> Vec<Option<rt::Function>> {
  //let mut dups_count = DupsCount::new();
  let mut funcs: Vec<Option<rt::Function>> = iter::repeat_with(|| None).take(65535).collect();
  for (name, rules_info) in &comp.rule_group {
    let fnid = comp.name_to_id.get(name).unwrap_or(&0);
    let func = build_runtime_function(comp, &rules_info.1);
    funcs[*fnid as usize] = Some(func);
  }
  funcs
}

fn build_runtime_function(
  comp: &rb::RuleBook,
  rules: &[lang::Rule],
) -> rt::Function {
  let dynfun = build_dynfun(comp, rules);

  let arity = dynfun.redex.len() as u64;
  let mut stricts = Vec::new();
  for (i, is_redex) in dynfun.redex.iter().enumerate() {
    if *is_redex {
      stricts.push(i as u64);
    }
  }

  let rewriter: rt::Rewriter = Box::new(move |mem, dups, host, term| {
    // For each argument, if it is a redex and a PAR, apply the cal_par rule
    for (i, redex) in dynfun.redex.iter().enumerate() {
      let i = i as u64;
      if *redex && rt::get_tag(rt::ask_arg(mem, term, i)) == rt::PAR {
        rt::cal_par(mem, host, term, rt::ask_arg(mem, term, i), i);
        return true;
      }
    }

    // For each rule condition vector
    for dynrule in &dynfun.rules {
      // Check if the rule matches
      let mut matched = true;

      // Tests each rule condition (ex: `get_tag(args[0]) == SUCC`)
      for (i, cond) in dynrule.cond.iter().enumerate() {
        let i = i as u64;
        match rt::get_tag(*cond) {
          rt::U32 => {
            //println!("Didn't match because of U32. i={} {} {}", i, rt::get_val(rt::ask_arg(mem, term, i)), rt::get_val(*cond));
            let same_tag = rt::get_tag(rt::ask_arg(mem, term, i)) == rt::U32;
            let same_val = rt::get_val(rt::ask_arg(mem, term, i)) == rt::get_val(*cond);
            matched = matched && same_tag && same_val;
          }
          rt::CTR => {
            //println!("Didn't match because of CTR. i={} {} {}", i, rt::get_tag(rt::ask_arg(mem, term, i)), rt::get_val(*cond));
            let same_tag = rt::get_tag(rt::ask_arg(mem, term, i)) == rt::CTR;
            let same_ext = rt::get_ext(rt::ask_arg(mem, term, i)) == rt::get_ext(*cond);
            matched = matched && same_tag && same_ext;
          }
          _ => {}
        }
      }

      // If all conditions are satisfied, the rule matched, so we must apply it
      if matched {
        // Increments the gas count
        rt::inc_cost(mem);

        // Builds the right-hand side term (ex: `(Succ (Add a b))`)
        let done = alloc_body(mem, term, &dynrule.body, &dynrule.vars, dups);

        // Links the host location to it
        rt::link(mem, host, done);

        // Clears the matched ctrs (the `(Succ ...)` and the `(Add ...)` ctrs)
        rt::clear(mem, rt::get_loc(term, 0), dynfun.redex.len() as u64);
        for (i, arity) in &dynrule.free {
          let i = *i as u64;
          rt::clear(mem, rt::get_loc(rt::ask_arg(mem, term, i), 0), *arity);
        }

        // Collects unused variables (none in this example)
        for dynvar @ DynVar { param: _, field: _, erase } in dynrule.vars.iter() {
          if *erase {
            rt::collect(mem, get_var(mem, term, dynvar));
          }
        }

        return true;
      }
    }
    false
  });

  rt::Function { arity, stricts, rewriter }
}

/// Converts a Lambolt Term to a Runtime Term
fn term_to_dynterm(comp: &rb::RuleBook, term: &lang::Term, free_vars: u64) -> DynTerm {
  fn convert_oper(oper: &lang::Oper) -> u64 {
    match oper {
      lang::Oper::Add => rt::ADD,
      lang::Oper::Sub => rt::SUB,
      lang::Oper::Mul => rt::MUL,
      lang::Oper::Div => rt::DIV,
      lang::Oper::Mod => rt::MOD,
      lang::Oper::And => rt::AND,
      lang::Oper::Or => rt::OR,
      lang::Oper::Xor => rt::XOR,
      lang::Oper::Shl => rt::SHL,
      lang::Oper::Shr => rt::SHR,
      lang::Oper::Ltn => rt::LTN,
      lang::Oper::Lte => rt::LTE,
      lang::Oper::Eql => rt::EQL,
      lang::Oper::Gte => rt::GTE,
      lang::Oper::Gtn => rt::GTN,
      lang::Oper::Neq => rt::NEQ,
    }
  }

  #[allow(clippy::identity_op)]
  fn convert_term(
    term: &lang::Term,
    comp: &rb::RuleBook,
    depth: u64,
    vars: &mut Vec<String>,
  ) -> DynTerm {
    match term {
      lang::Term::Var { name } => {
        if let Some((idx,_)) = vars.iter().enumerate().rev().find(|(_, var)| var == &name) {
          DynTerm::Var{ bidx: idx as u64 }
        } else {
          DynTerm::Glo{ name: name.clone() }
        }
      },
      lang::Term::Dup { nam0, nam1, expr, body } => {
        let eras = (nam0 == "*", nam1 == "*");
        let expr = Box::new(convert_term(expr, comp, depth + 0, vars));
        vars.push(nam0.clone());
        vars.push(nam1.clone());
        let body = Box::new(convert_term(body, comp, depth + 2, vars));
        vars.pop();
        vars.pop();
        DynTerm::Dup { eras, expr, body }
      }
      lang::Term::Lam { name, body } => {
        let glob = if rb::is_global_name(&name) { Some(name.clone()) } else { None };
        let eras = name == "*";
        vars.push(name.clone());
        let body = Box::new(convert_term(body, comp, depth + 1, vars));
        vars.pop();
        DynTerm::Lam { eras, glob, body }
      }
      lang::Term::Let { name, expr, body } => {
        let expr = Box::new(convert_term(expr, comp, depth + 0, vars));
        vars.push(name.clone());
        let body = Box::new(convert_term(body, comp, depth + 1, vars));
        vars.pop();
        DynTerm::Let { expr, body }
      }
      lang::Term::App { func, argm } => {
        let func = Box::new(convert_term(func, comp, depth + 0, vars));
        let argm = Box::new(convert_term(argm, comp, depth + 0, vars));
        DynTerm::App { func, argm }
      }
      lang::Term::Ctr { name, args } => {
        let term_func =
          *comp.name_to_id.get(name).unwrap_or_else(|| panic!("Unbound symbol: {}", name));
        let term_args = args.iter().map(|arg| convert_term(arg, comp, depth + 0, vars)).collect();
        if *comp.ctr_is_cal.get(name).unwrap_or(&false) {
          DynTerm::Cal { func: term_func, args: term_args }
        } else {
          DynTerm::Ctr { func: term_func, args: term_args }
        }
      }
      lang::Term::U32 { numb } => DynTerm::U32 { numb: *numb },
      lang::Term::Op2 { oper, val0, val1 } => {
        let oper = convert_oper(oper);
        let val0 = Box::new(convert_term(val0, comp, depth + 0, vars));
        let val1 = Box::new(convert_term(val1, comp, depth + 1, vars));
        DynTerm::Op2 { oper, val0, val1 }
      }
    }
  }

  let mut vars = (0..free_vars).map(|i| format!("x{}", i)).collect();
  convert_term(term, comp, 0, &mut vars)
}

fn build_body(term: &DynTerm, free_vars: u64) -> Body {
  #[derive(Clone, Debug)]
  enum PreElem {
    Fix { value: u64 },
    Loc { value: u64, targ: u64, slot: u64 },
    Ext { index: u64 },
    Glo { name: String },
  }
  type PreNode = Vec<PreElem>;
  fn link(nodes: &mut Vec<PreNode>, targ: u64, slot: u64, elem: PreElem) {
    nodes[targ as usize][slot as usize] = elem.clone();
    if let PreElem::Loc { value, targ: var_targ, slot: var_slot } = elem {
      let tag = rt::get_tag(value);
      if tag <= rt::VAR {
        nodes[var_targ as usize][(var_slot + (tag & 0x01)) as usize] = PreElem::Loc { value: rt::Arg(0), targ, slot };
      }
    }
  }
  fn gen_elem(
    term: &DynTerm,
    glob: &mut HashMap<String, PreElem>,
    vars: &mut Vec<PreElem>,
    nodes: &mut Vec<PreNode>,
  ) -> PreElem {
    match term {
      DynTerm::Var { bidx } => {
        if *bidx < vars.len() as u64 {
          vars[*bidx as usize].clone()
        } else {
          panic!("Unbound variable.");
        }
      }
      DynTerm::Glo { name } => {
        PreElem::Glo {
          name: name.clone()
        }
      }
      DynTerm::Dup { eras: _, expr, body } => {
        let targ = nodes.len() as u64;
        nodes.push(vec![PreElem::Fix { value: 0 }; 3]);
        //let dupk = dups_count.next();
        link(nodes, targ, 0, PreElem::Fix { value: rt::Era() });
        link(nodes, targ, 1, PreElem::Fix { value: rt::Era() });
        let expr = gen_elem(expr, glob, vars, nodes);
        link(nodes, targ, 2, expr);
        vars.push(PreElem::Loc { value: rt::Dp0(0, 0), targ, slot: 0 });
        vars.push(PreElem::Loc { value: rt::Dp1(0, 0), targ, slot: 0 });
        let body = gen_elem(body, glob, vars, nodes);
        vars.pop();
        vars.pop();
        body
      }
      DynTerm::Let { expr, body } => {
        let expr = gen_elem(expr, glob, vars, nodes);
        vars.push(expr);
        let body = gen_elem(body, glob, vars, nodes);
        vars.pop();
        body
      }
      DynTerm::Lam { eras: _, glob: glob_name, body } => {
        let targ = nodes.len() as u64;
        nodes.push(vec![PreElem::Fix { value: 0 }; 2]);
        link(nodes, targ, 0, PreElem::Fix { value: rt::Era() });
        if let Some(glob_name) = glob_name {
          glob.insert(glob_name.clone(), PreElem::Loc { value: rt::Var(0), targ, slot: 0 });
        }
        vars.push(PreElem::Loc { value: rt::Var(0), targ, slot: 0 });
        let body = gen_elem(body, glob, vars, nodes);
        link(nodes, targ, 1, body);
        vars.pop();
        PreElem::Loc { value: rt::Lam(0), targ, slot: 0 }
      }
      DynTerm::App { func, argm } => {
        let targ = nodes.len() as u64;
        nodes.push(vec![PreElem::Fix { value: 0 }; 2]);
        let func = gen_elem(func, glob, vars, nodes);
        link(nodes, targ, 0, func);
        let argm = gen_elem(argm, glob, vars, nodes);
        link(nodes, targ, 1, argm);
        PreElem::Loc { value: rt::App(0), targ, slot: 0 }
      }
      DynTerm::Cal { func, args } => {
        if !args.is_empty() {
          let targ = nodes.len() as u64;
          nodes.push(vec![PreElem::Fix { value: 0 }; args.len() as usize]);
          for (i, arg) in args.iter().enumerate() {
            let arg = gen_elem(arg, glob, vars, nodes);
            link(nodes, targ, i as u64, arg);
          }
          PreElem::Loc { value: rt::Cal(args.len() as u64, *func, 0), targ, slot: 0 }
        } else {
          PreElem::Fix { value: rt::Cal(0, *func, 0) }
        }
      }
      DynTerm::Ctr { func, args } => {
        if !args.is_empty() {
          let targ = nodes.len() as u64;
          nodes.push(vec![PreElem::Fix { value: 0 }; args.len() as usize]);
          for (i, arg) in args.iter().enumerate() {
            let arg = gen_elem(arg, glob, vars, nodes);
            link(nodes, targ, i as u64, arg);
          }
          PreElem::Loc { value: rt::Ctr(args.len() as u64, *func, 0), targ, slot: 0 }
        } else {
          PreElem::Fix { value: rt::Ctr(0, *func, 0) }
        }
      }
      DynTerm::U32 { numb } => PreElem::Fix { value: rt::U_32(*numb as u64) },
      DynTerm::Op2 { oper, val0, val1 } => {
        let targ = nodes.len() as u64;
        nodes.push(vec![PreElem::Fix { value: 0 }; 2]);
        let val0 = gen_elem(val0, glob, vars, nodes);
        link(nodes, targ, 0, val0);
        let val1 = gen_elem(val1, glob, vars, nodes);
        link(nodes, targ, 1, val1);
        PreElem::Loc { value: rt::Op2(*oper, 0), targ, slot: 0 }
      }
    }
  }
  fn make_elem(pre_elem: &PreElem, glob: &HashMap<String,PreElem>) -> Elem {
    match pre_elem {
      PreElem::Fix { value } => {
        Elem::Fix {
          value: *value
        }
      },
      PreElem::Loc { value, targ, slot } => {
        Elem::Loc {
          value: *value,
          targ: *targ,
          slot: *slot
        }
      },
      PreElem::Ext { index } => {
        Elem::Ext {
          index: *index
        }
      },
      PreElem::Glo { name } => {
        println!("Finding global: {}", name);
        if let Some(got) = glob.get(name) {
          println!("found!");
          make_elem(got, glob)
        } else {
          panic!("Unbound variable: {}", name)
        }
      },
    }
  }
  let mut pre_nodes: Vec<PreNode> = Vec::new();
  let mut vars: Vec<PreElem> = (0..free_vars).map(|i| PreElem::Ext { index: i }).collect();
  let mut glob: HashMap<String,PreElem> = HashMap::new();
  let pre_elem = gen_elem(term, &mut glob, &mut vars, &mut pre_nodes);
  let mut nodes: Vec<Node> = Vec::new();
  for pre_node in pre_nodes {
    let mut node = Vec::new();
    for pre_elem in pre_node {
      node.push(make_elem(&pre_elem, &glob));
    }
    nodes.push(node);
  }
  (make_elem(&pre_elem, &glob), nodes)
}

static mut ALLOC_BODY_WORKSPACE: &mut [u64] = &mut [0; 256 * 256 * 256]; // to avoid dynamic allocations
fn alloc_body(mem: &mut rt::Worker, term: rt::Lnk, body: &Body, vars: &[DynVar], dups: &mut u64) -> rt::Lnk {
  unsafe {
    let (elem, nodes) = body;
    let hosts = &mut ALLOC_BODY_WORKSPACE;
    nodes.iter().enumerate().for_each(|(i, node)| {
      hosts[i] = rt::alloc(mem, node.len() as u64);
    });
    nodes.iter().enumerate().for_each(|(i, node)| {
      let host = hosts[i] as usize;
      node.iter().enumerate().for_each(|(j, elem)| match elem {
        Elem::Fix { value } => {
          mem.node[host + j] = *value;
        }
        Elem::Ext { index } => {
          rt::link(mem, (host + j) as u64, get_var(mem, term, &vars[*index as usize]));
        }
        Elem::Loc { value, targ, slot } => {
          let mut val = value + hosts[*targ as usize] + slot;
          if rt::get_tag(*value) == rt::DP0 {
            val += (*dups & 0xFFFFFF) * rt::EXT; // FIXME: should be changed if the pointer format changes
          }
          if rt::get_tag(*value) == rt::DP1 {
            val += (*dups & 0xFFFFFF) * rt::EXT; // FIXME: should be changed if the pointer format changes
            *dups += 1;
          }
          mem.node[host + j] = val;
        }
      });
    });
    match elem {
      Elem::Fix { value } => *value,
      Elem::Ext { index } => get_var(mem, term, &vars[*index as usize]),
      Elem::Loc { value, targ, slot } => value + hosts[*targ as usize] + slot,
    }
  }
}

fn alloc_closed_dynterm(mem: &mut rt::Worker, term: &DynTerm) -> u64 {
  let mut dups = 0;
  let host = rt::alloc(mem, 1);
  let body = build_body(term, 0);
  let term = alloc_body(mem, 0, &body, &[], &mut dups);
  rt::link(mem, host, term);
  host
}

fn alloc_term(
  mem: &mut rt::Worker,
  comp: &rb::RuleBook,
  term: &lang::Term,
) -> u64 {
  alloc_closed_dynterm(mem, &term_to_dynterm(comp, term, 0))
}

// Evaluates a Lambolt term to normal form
pub fn eval_code(call: &lang::Term, code: &str, debug: bool) -> Result<(Box<lang::Term>, u64, u64, u64), String> {
  // Creates a new Runtime worker
  let mut worker = rt::new_worker();

  // Parses and reads the input file
  let file = lang::read_file(code)?;

  // Converts the Lambolt file to a rulebook file
  let book = rb::gen_rulebook(&file);

  // Builds dynamic functions
  let funs = build_runtime_functions(&book);

  // Allocates the main term
  let host = alloc_term(&mut worker, &book, call);

  // Normalizes it
  let init = Instant::now();
  rt::normal(&mut worker, host, &funs, Some(&book.id_to_name), debug);
  let time = init.elapsed().as_millis() as u64;

  // Reads it back to a Lambolt string
  let norm = rd::as_term(&worker, &Some(book), host)?;

  // Returns the normal form and the gas cost
  Ok((norm, worker.cost, worker.size, time))
}
