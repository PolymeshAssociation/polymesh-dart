use test_log::test;

use curve_tree_relations::curve_tree::SelRerandParameters;

use polymesh_dart::NodeLevel;
use polymesh_dart::curve_tree::{
    AccountTreeConfig, CompressedCurveTreeRoot, CurveTreeRoot, FullCurveTree, LeafValue,
    LeanCurveTree,
};
use polymesh_dart::{PallasA, PallasParameters, VestaParameters};

const L: usize = 16;
const HEIGHT: NodeLevel = 4;
const GENS_LENGTH: usize = 32;

fn create_test_leaf(value: usize) -> LeafValue<PallasParameters> {
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_pallas::Fr as PallasScalar;

    // Create a deterministic leaf value for testing
    let scalar = PallasScalar::from(value as u64);
    (PallasA::generator() * scalar).into_affine().into()
}

fn setup_trees() -> (
    LeanCurveTree<L, 1, AccountTreeConfig>,
    FullCurveTree<L, 1, AccountTreeConfig>,
    CompressedCurveTreeRoot<L, 1>,
    SelRerandParameters<PallasParameters, VestaParameters>,
) {
    let mut storage_tree =
        FullCurveTree::<L, 1, AccountTreeConfig>::new_with_capacity(HEIGHT, GENS_LENGTH)
            .expect("Failed to create storage tree");
    assert!(storage_tree.height() == HEIGHT);
    let params = storage_tree.params().clone();

    let mut compressed_root = CompressedCurveTreeRoot::new::<PallasParameters, VestaParameters>();
    let mut lean_tree =
        LeanCurveTree::<L, 1, AccountTreeConfig>::new(HEIGHT, &params, &mut compressed_root)
            .expect("Failed to create lean tree");
    assert!(lean_tree.height() == HEIGHT);

    // Insert a leaf into both trees to avoid empty tree edge cases
    let leaf = create_test_leaf(0);
    lean_tree
        .append_leaf(leaf, &params, &mut compressed_root)
        .unwrap();
    storage_tree.insert(leaf).unwrap();

    // Compare roots
    let lean_root = compressed_root
        .root_node::<AccountTreeConfig>()
        .expect("Failed to get compressed root");
    let storage_root = storage_tree
        .root_node()
        .expect("Failed to get storage root");

    assert_roots_equal(&lean_root, &storage_root, &format!("on initial trees"));

    (lean_tree, storage_tree, compressed_root, params)
}

/// Compare two roots, printing debug info on mismatch since Root doesn't implement Debug
fn assert_roots_equal(
    lean_root: &CurveTreeRoot<L, 1, AccountTreeConfig>,
    storage_root: &CurveTreeRoot<L, 1, AccountTreeConfig>,
    context: &str,
) {
    let lean_root = lean_root.decode().expect("Failed to decode full root");
    let storage_root = storage_root
        .decode()
        .expect("Failed to decode storage root");
    let roots_match = match (&lean_root, &storage_root) {
        (
            curve_tree_relations::curve_tree::Root::Even(full),
            curve_tree_relations::curve_tree::Root::Even(storage),
        ) => {
            full.commitments == storage.commitments
                && full.x_coord_children == storage.x_coord_children
        }
        (
            curve_tree_relations::curve_tree::Root::Odd(full),
            curve_tree_relations::curve_tree::Root::Odd(storage),
        ) => {
            full.commitments == storage.commitments
                && full.x_coord_children == storage.x_coord_children
        }
        _ => false,
    };

    if !roots_match {
        eprintln!("full tree root: {:#?}", lean_root);
        eprintln!("storage tree root: {:#?}", storage_root);
        panic!("Roots differ: {}", context);
    }
}

/// Test insertion of leafs into `CurveTreeStorage` against the `FullCurveTree` implementation.
#[test]
fn test_inserts() {
    let (mut lean_tree, mut storage_tree, mut compressed_root, params) = setup_trees();

    // Test inserting a few leaves and comparing roots
    for i in 1..=5 {
        let leaf = create_test_leaf(i);

        // Insert into both trees
        lean_tree
            .append_leaf(leaf, &params, &mut compressed_root)
            .unwrap();
        storage_tree.insert(leaf).unwrap();

        // Compare roots
        let lean_root = compressed_root
            .root_node()
            .expect("Failed to get full root");
        let storage_root = storage_tree
            .root_node()
            .expect("Failed to get storage root");

        assert_roots_equal(
            &lean_root,
            &storage_root,
            &format!("after inserting leaf {}", i),
        );
    }
}

/// Test that both trees can grow beyond the initial L capacity
#[test]
fn test_growth_beyond_l() {
    let (mut lean_tree, mut storage_tree, mut compressed_root, params) = setup_trees();

    // Insert more leaves than L to test growth
    let num_leaves = L * 2 + 3; // 11 leaves when L=4

    for i in 1..=num_leaves {
        let leaf = create_test_leaf(i);

        // Insert into both trees
        lean_tree
            .append_leaf(leaf, &params, &mut compressed_root)
            .unwrap();
        storage_tree.insert(leaf).unwrap();

        // Compare roots after each insertion
        let lean_root = compressed_root
            .root_node()
            .expect("Failed to get full root");
        let storage_root = storage_tree
            .root_node()
            .expect("Failed to get storage root");

        assert_roots_equal(
            &lean_root,
            &storage_root,
            &format!("after inserting {} leaves", i),
        );
    }
}

/// Test large tree growth
#[test]
fn test_large_tree_growth() {
    let (mut lean_tree, mut storage_tree, mut compressed_root, params) = setup_trees();

    // Insert a larger number of leaves to test scalability
    let num_leaves = L * 4; // 16 leaves when L=4

    for i in 1..=num_leaves {
        let leaf = create_test_leaf(i);

        lean_tree
            .append_leaf(leaf, &params, &mut compressed_root)
            .unwrap();
        storage_tree.insert(leaf).unwrap();

        // Check roots every few insertions to catch issues early
        if i % L == 0 {
            let lean_root = compressed_root
                .root_node()
                .expect("Failed to get full root");
            let storage_root = storage_tree
                .root_node()
                .expect("Failed to get storage root");
            assert_roots_equal(&lean_root, &storage_root, &format!("after {} leaves", i));
        }
    }

    // Final root check
    let lean_root = compressed_root
        .root_node()
        .expect("Failed to get full root");
    let storage_root = storage_tree
        .root_node()
        .expect("Failed to get storage root");
    assert_roots_equal(
        &lean_root,
        &storage_root,
        &format!("final with {} leaves", num_leaves),
    );
}
