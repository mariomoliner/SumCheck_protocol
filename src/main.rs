use std::{usize};
use ark_ff::Field;
use ark_poly::{
    polynomial::multivariate::{SparsePolynomial, SparseTerm, Term}, univariate::SparsePolynomial as uniSparsePolynomial, MVPolynomial, Polynomial, 
};
use ark_bls12_381::{Fq as BaseField,FQ_ONE,FQ_ZERO};
use ark_std::{UniformRand, test_rng, Zero, rand::rngs::StdRng};

use sha2::{Sha256, Digest};
use std::fmt;

#[derive(Debug)]
struct MultivariatePolynomial(SparsePolynomial<BaseField, SparseTerm>);
struct UnivariatePolynomial(uniSparsePolynomial<BaseField>);

struct NonInteractiveProof {
    s1: BaseField,
    gj: Vec<UnivariatePolynomial>
}


impl fmt::Display for MultivariatePolynomial {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {

        let mut poly_string: String = String::new();

        for term in self.0.terms(){
            let s = term.0.to_string();
            let vars = term.1.iter().map(|&(var,exp)| format!("(X_{})^{}", var, exp)).collect::<Vec<String>>().join("*");
            
            if(!poly_string.is_empty()){
                poly_string.push_str(" + ");
            }

            poly_string.push_str(&s);
            poly_string.push_str("*");
            poly_string.push_str(&vars);
        }
        write!(f, "{}", poly_string)
    }
}


impl fmt::Display for UnivariatePolynomial {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {

        let mut poly_string: String = String::new();

        for (exp, coeff) in self.0.to_vec(){
            if(!poly_string.is_empty()){
                poly_string.push_str(" + ");
            }
            poly_string.push_str(&coeff.to_string());
            poly_string.push_str("*X^");
            poly_string.push_str(&exp.to_string());
        }  

        write!(f, "{}", poly_string) 
    
    }
}




//generates boolean hypercube over the BaseField
fn generate_vectors(n: usize, current: &mut Vec<BaseField>) -> Vec<Vec<BaseField>> {
    if n == 0 {
        vec![current.clone()]
    } else {
        let mut result = Vec::new();
        for &value in &[FQ_ONE, FQ_ZERO] {
            current.push(value);
            result.extend(generate_vectors(n - 1, current));
            current.pop();
        }
        result
    }
}

// returns the result of evaluating the polynomial over the boolean hypercube
fn evaluate_poly_hypercube(poly: &SparsePolynomial<BaseField,SparseTerm>) -> BaseField{
    let num_vars = poly.num_vars();
    let mut current_vector = Vec::new();
    let boolean_hypercube = generate_vectors(num_vars, &mut current_vector);

    let result : BaseField =  boolean_hypercube.into_iter().map(|n| poly.evaluate(&n)).sum();
    return result;
}

// return the polynomial degree in the variable i
fn get_poly_degree_i(poly: &SparsePolynomial<BaseField,SparseTerm>, i : usize) -> usize{
    let mut max = 0;
    for (_scalar, terms) in poly.terms(){
        for (_pos, e) in terms.iter().enumerate() {
            if e.0 == i-1 && e.1 > max {
                max = e.1;
            }
        }
    }
    return max;
}

// evaluates and returns the polynomial on all variables except j with the given vector
fn evaluate_poly_j(poly : &SparsePolynomial<BaseField,SparseTerm>, j: usize, vector : &mut Vec<BaseField>) -> uniSparsePolynomial<BaseField> {
    let mut result = uniSparsePolynomial::zero();

    //the variable to not be evaluate is set to one to get the rest of coefficients
    vector[j-1] = FQ_ONE;
    

    for (scalar_coeff, term) in poly.terms(){
        let evaluation = term.evaluate(&vector);
        let power = match term
            .vars()
            .iter()
            .zip(term.powers().iter())
            .find(|(&v, _)| v == j-1)
        {
            Some((_, p)) => *p,
            None => 0,
        };
        let new_term_coeff = *scalar_coeff * evaluation;
        result = result + uniSparsePolynomial::from_coefficients_slice(&[(power, new_term_coeff)]);
    }

    return result;
}

// return the univariate polynomial on the variable j evaluating on the left the vector r  and on the right the hypercube boolean. They are added and returned 
fn get_poly_j(poly : &SparsePolynomial<BaseField,SparseTerm>, r:  Vec<BaseField>, j : usize) -> uniSparsePolynomial<ark_ff::Fp384<ark_bls12_381::FqParameters>> {
    let mut current_vector = Vec::new();

    let boolean_hypercube = generate_vectors(poly.num_vars()-r.len()-1, &mut current_vector);
    //println!("{:}",boolean_hypercube[1][0]);

    let mut final_sum: uniSparsePolynomial<ark_ff::Fp384<ark_bls12_381::FqParameters>> = uniSparsePolynomial::zero();

    for vec in boolean_hypercube{
        let mut appended_vector = [r.clone(),vec![FQ_ONE],vec].concat();

        let uni_poly: uniSparsePolynomial<ark_ff::Fp384<ark_bls12_381::FqParameters>> = evaluate_poly_j(&poly, j, &mut appended_vector);

        final_sum = final_sum + uni_poly;
    }

    return final_sum;
}

// gets a random Basefield scalar
fn get_rand_scalar(rng : &mut StdRng) -> BaseField{
    let random_scalar = BaseField::rand(rng);

    return random_scalar;
}

// return the Basefield analog from a hash result
fn hash_to_basefield(hash: &[u8]) -> BaseField {
    let prueba = BaseField::from_random_bytes(&hash);

    prueba.unwrap()
}

// from a polynomial and the sum over the boolean hypercube return an instance of NonInteractiveProof
fn get_non_interactive_proof(poly : &MultivariatePolynomial, c1: BaseField) -> NonInteractiveProof{
    let l = poly.0.num_vars;
    let mut r : Vec<BaseField> = vec![];
    let mut gj;
    let mut rj : BaseField;

    let mut proof = NonInteractiveProof {
        s1 : c1,
        gj: Vec::with_capacity(l)
    };

    let mut hasher = Sha256::new();
    gj = get_poly_j(&poly.0, r.clone(), 1);
    proof.gj.push(UnivariatePolynomial((gj.clone())));

    hasher.update(UnivariatePolynomial(gj).to_string());
    rj = hash_to_basefield(&hasher.finalize());
    r.push(rj);

    for j in 2..=l{
        let mut hasher = Sha256::new();

        gj = get_poly_j(&poly.0, r.clone(), j);
        proof.gj.push(UnivariatePolynomial((gj)));

        for polynomial in &proof.gj{
            hasher.update(polynomial.to_string());
        }
        rj = hash_to_basefield(&hasher.finalize());
        r.push(rj);
    }

    proof
}

// runs the verifier for the polynomial and the basefield hypercube solution provided
fn verify(poly: &SparsePolynomial<BaseField, SparseTerm>, c1: BaseField) -> bool{
    let rng = &mut test_rng();
    let mut r : Vec<BaseField> = vec![];
    let mut gj;
    let mut cj: BaseField;
    let mut rj : BaseField;

    gj = get_poly_j(&poly, r.clone(), 1);
    assert_eq!(c1,gj.evaluate(&FQ_ONE) + gj.evaluate(&FQ_ZERO), "step 1 with g1 not verified!");
    assert!(gj.degree() <= get_poly_degree_i(poly, 1), "step 1 with g1 not verified!");
    rj = get_rand_scalar(rng);
    r.push(rj);
    

    for j in 2..poly.num_vars(){
        cj = gj.evaluate(&rj);
        gj = get_poly_j(&poly, r.clone(), j);
        assert_eq!(cj,gj.evaluate(&FQ_ONE) + gj.evaluate(&FQ_ZERO), "step {} failed to verify!",j);
        assert!(gj.degree() <= get_poly_degree_i(poly, j), "step {} failed to verify!",j);

        rj = get_rand_scalar(rng);
        r.push(rj);
    }

    cj = gj.evaluate(&rj);
    gj = get_poly_j(&poly, r.clone(), poly.num_vars());

    assert_eq!(cj,gj.evaluate(&FQ_ONE) + gj.evaluate(&FQ_ZERO), "step {} failed to verify!", poly.num_vars());
    assert!(gj.degree() <= get_poly_degree_i(poly, poly.num_vars()) , "step {} failed to verify!", poly.num_vars());


    rj = get_rand_scalar(rng);
    r.push(rj);
    let g_evaluated_over_rs = poly.evaluate(&r);
    assert_eq!(gj.evaluate(&rj),  g_evaluated_over_rs, "failed last step");

    return true;
    
}

// runs the verifier in non interactive mode
fn verify_non_interactive(poly: MultivariatePolynomial, c1: BaseField) -> bool{
    let num_vars = poly.0.num_vars();
    let proof = get_non_interactive_proof(&poly, c1);
    let mut r : BaseField = BaseField::from(0);
    let mut rs : Vec<BaseField> = Vec::new();

    assert!(proof.gj[0].0.degree() <= get_poly_degree_i(&poly.0, 1), "step {} failed to verify!", 1);
    assert_eq!(c1,proof.gj[0].0.evaluate(&FQ_ONE) + proof.gj[0].0.evaluate(&FQ_ZERO), "step {} with g1 not verified!", 1);

    for j in 0..=num_vars-1{
        let mut hasher = Sha256::new();

        for i in 0..=j{
            hasher.update(proof.gj[i].to_string().as_bytes());
        }
        r = hash_to_basefield(&hasher.finalize());
        rs.push(r);

        if(j != num_vars-1){
            assert!(proof.gj[j].0.degree() <= get_poly_degree_i(&poly.0, j+1), "step {} failed to verify!", j);
            assert_eq!(proof.gj[j].0.evaluate(&r),proof.gj[j+1].0.evaluate(&FQ_ONE) + proof.gj[j+1].0.evaluate(&FQ_ZERO), "step {} with g1 not verified!", j);
        }
    }

    let g_evaluated_over_rs = poly.0.evaluate(&rs);
    assert!(proof.gj[num_vars-1].0.degree() <= get_poly_degree_i(&poly.0, num_vars), "last step failed to verify!");
    assert_eq!(proof.gj[num_vars-1].0.evaluate(&r), g_evaluated_over_rs, "last step with g not verified!");

    true

}

// Some example polynomials runned over the verifier.
fn verify_example(){
    // Thaler book example: g(x1,x2,x3) = 2x1^3 + x1x3 + x2x3
    let polynomial= SparsePolynomial::from_coefficients_vec(
        3,
        vec![
            (BaseField::from(2), SparseTerm::new(vec![(0, 3)])),
            (BaseField::from(1), SparseTerm::new(vec![(0, 1), (2, 1)])),
            (BaseField::from(1), SparseTerm::new(vec![(1, 1), (2, 1)])),
        ],
    );

    let c1 = evaluate_poly_hypercube(&polynomial);
    match verify(&polynomial, c1){
        true =>  println!("Verified the hypercube sum is correct!"),
        false => println!("The hypercube failed to be verified!")
    }
}

// Another example with more variables
fn verify_example_2(){
    // g(x1,x2,x3,x4,x5,x6,x7,x8) = x1^3*x3 + x2*x3*x4^2*x5^3 + x6*x7 + x8+x5^2 + 4
    let polynomial= SparsePolynomial::from_coefficients_vec(
        8,
        vec![
            (BaseField::from(6), SparseTerm::new(vec![(0, 3),(2,1)])),
            (BaseField::from(1), SparseTerm::new(vec![(1, 1), (2, 1),(3,2),(4,3)])),
            (BaseField::from(1), SparseTerm::new(vec![(5, 1), (6, 1)])),
            (BaseField::from(1), SparseTerm::new(vec![(7, 1), (4, 2)])),
            (BaseField::from(4), SparseTerm::new(vec![])),
        ],
    );

    let c1 = evaluate_poly_hypercube(&polynomial);
    match verify(&polynomial, c1){
        true =>  println!("Verified the hypercube sum is correct!"),
        false => println!("The hypercube failed to be verified!")
    }
}

//example of non interactive proof
fn verify_example_non_interactive(){
    let polynomial= MultivariatePolynomial(SparsePolynomial::from_coefficients_vec(
        3,
        vec![
            (BaseField::from(2), SparseTerm::new(vec![(0, 3)])),
            (BaseField::from(1), SparseTerm::new(vec![(0, 1), (2, 1)])),
            (BaseField::from(1), SparseTerm::new(vec![(1, 1), (2, 1)])),
        ],
    ));

    let c1 = evaluate_poly_hypercube(&polynomial.0);

    match verify_non_interactive(polynomial, c1){
        true =>  println!("Verified the hypercube sum is correct!"),
        false => println!("The hypercube failed to be verified!")
    }
}

fn main() {
    //verify_example();
    //verify_example_2();

    verify_example_non_interactive();

}