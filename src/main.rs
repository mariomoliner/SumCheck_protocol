use std::usize;
use ark_ff::Field;
use ark_poly::{
    polynomial::multivariate::{SparsePolynomial, SparseTerm, Term}, univariate::SparsePolynomial as uniSparsePolynomial, MVPolynomial, Polynomial, 
};
use ark_bls12_381::{Fq as BaseField,FQ_ONE,FQ_ZERO};
use ark_std::{UniformRand, test_rng, Zero, rand::rngs::StdRng};

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
    for (scalar, terms) in poly.terms(){
        for (pos, e) in terms.iter().enumerate() {
            if(e.0 == i-1 && e.1 > max){
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

    let mut boolean_hypercube = generate_vectors(poly.num_vars()-r.len()-1, &mut current_vector);
    //println!("{:}",boolean_hypercube[1][0]);

    let mut final_sum: uniSparsePolynomial<ark_ff::Fp384<ark_bls12_381::FqParameters>> = uniSparsePolynomial::zero();

    for vec in boolean_hypercube{
        let mut appended_vector = [r.clone(),vec![FQ_ONE],vec].concat();

        let uni_poly: uniSparsePolynomial<ark_ff::Fp384<ark_bls12_381::FqParameters>> = evaluate_poly_j(&poly, j, &mut appended_vector);

        final_sum = final_sum + uni_poly;
    }

    return final_sum;
}

fn get_rand_scalar(rng : &mut StdRng) -> BaseField{
    let random_scalar = BaseField::rand(rng);

    return random_scalar;
}


//runs the verifier for the polynomial and the boolean hypercube provided
fn verify(poly: &SparsePolynomial<BaseField, SparseTerm>, c1: BaseField) -> bool{
    let rng = &mut test_rng();
    let mut r : Vec<BaseField> = vec![];
    let mut gj;
    let mut cj: BaseField;
    let mut rj : BaseField;

    gj = get_poly_j(&poly, r.clone(), 1);
    assert_eq!(c1,gj.evaluate(&FQ_ONE) + gj.evaluate(&FQ_ZERO), "step 1 with g1 not verified!");
    assert!(get_poly_degree_i(poly, 1) <= poly.degree(), "step 1 with g1 not verified!");
    rj = BaseField::from(2);
    r.push(rj);

    

    for j in 2..poly.num_vars(){
        let cj = gj.evaluate(&rj);
        gj = get_poly_j(&poly, r.clone(), j);
        assert_eq!(cj,gj.evaluate(&FQ_ONE) + gj.evaluate(&FQ_ZERO), "step {} failed to verify!",j);
        assert!(get_poly_degree_i(poly, j) <= poly.degree(), "step {} failed to verify!",j);

        rj = get_rand_scalar(rng);
        r.push(rj);
    }

    cj = gj.evaluate(&rj);
    gj = get_poly_j(&poly, r.clone(), poly.num_vars());

    assert_eq!(cj,gj.evaluate(&FQ_ONE) + gj.evaluate(&FQ_ZERO), "step {} failed to verify!", poly.num_vars());
    assert!(get_poly_degree_i(poly, poly.num_vars()) <= poly.degree(), "step {} failed to verify!", poly.num_vars());


    rj = get_rand_scalar(rng);
    r.push(rj);
    let g_evaluated_over_rs = poly.evaluate(&r);
    assert_eq!(gj.evaluate(&rj),  g_evaluated_over_rs, "failed last step");

    return true;
    
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


fn main() {
    verify_example();
    //verify_example_2();
}