use test_log::test;

use ark_ec::AffineRepr;
use curve_tree_relations::curve_tree::{CurveTree, SelRerandParameters};

use polymesh_dart::curve_tree::{
    CurveTreeParameters, CurveTreePath, CurveTreeRoot, FullCurveTree, LeafValue,
};
use polymesh_dart::{Error, LeafIndex, NodeLevel};
use polymesh_dart::{PallasA, PallasParameters, VestaParameters};

const L: usize = 16;
const HEIGHT: NodeLevel = 4;
const GENS_LENGTH: usize = 32;

/// A Full Curve Tree that support both insertion and updates.
pub struct CurveTreeOld<const L: usize> {
    tree: CurveTree<L, 1, PallasParameters, VestaParameters>,
    height: usize,
    leaves: Vec<PallasA>,
    length: usize,
    params: CurveTreeParameters,
}

impl<const L: usize> std::fmt::Debug for CurveTreeOld<L> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FullCurveTree")
            .field("tree", &self.tree)
            .field("height", &self.height)
            .field("length", &self.length)
            .field("leaves", &self.leaves)
            .finish()
    }
}

impl<const L: usize> CurveTreeOld<L> {
    /// Creates a new instance of `FullCurveTree` with the given height and generators length.
    pub fn new_with_capacity(height: usize, gens_length: usize) -> Self {
        let params = SelRerandParameters::new(gens_length, gens_length);
        Self {
            tree: CurveTree::from_leaves(&[PallasA::zero()], &params, Some(height)),
            leaves: vec![],
            length: 0,
            height,
            params,
        }
    }

    pub fn height(&self) -> usize {
        self.tree.height()
    }

    /// Insert a new leaf into the curve tree.
    pub fn insert(&mut self, leaf: LeafValue<PallasParameters>) -> Result<usize, Error> {
        let leaf_index = self.length;
        self.update(leaf, leaf_index)?;

        self.length += 1;

        Ok(leaf_index)
    }

    /// Updates an existing leaf in the curve tree.
    pub fn update(
        &mut self,
        leaf: LeafValue<PallasParameters>,
        leaf_index: usize,
    ) -> Result<(), Error> {
        let leaf = *leaf;
        let cap = self.leaves.len();
        if leaf_index >= cap {
            self.grow(leaf_index);
        }

        match self.leaves.get_mut(leaf_index) {
            Some(old_leaf) => {
                *old_leaf = leaf;
            }
            None => {
                return Err(Error::LeafNotFound(leaf.into()));
            }
        }
        self.tree.update_leaf(leaf_index, 0, leaf, &self.params);
        Ok(())
    }

    /// Grows the leaves vector to accommodate more leaves.
    pub fn grow(&mut self, last_leaf_index: usize) {
        if last_leaf_index < self.leaves.len() {
            return;
        }
        let new_cap = last_leaf_index + 1;
        self.leaves.resize(new_cap, PallasA::zero());
        let new_tree = CurveTree::from_leaves(&self.leaves, &self.params, Some(self.height));
        self.tree = new_tree;
    }

    /// Returns the path to a leaf in the curve tree by its index.
    pub fn get_path_to_leaf_index(&self, leaf_index: usize) -> Result<CurveTreePath<L>, Error> {
        Ok(self.tree.get_path_to_leaf_for_proof(leaf_index, 0))
    }

    /// Returns the parameters of the curve tree.
    pub fn params(&self) -> &CurveTreeParameters {
        &self.params
    }

    /// Get the root node of the curve tree.
    pub fn root_node(&self) -> CurveTreeRoot<L> {
        CurveTreeRoot::new(&self.tree.root_node()).expect("Failed to get root node")
    }
}

fn create_test_leaf(value: usize) -> LeafValue<PallasParameters> {
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_pallas::Fr as PallasScalar;

    // Create a deterministic leaf value for testing
    let scalar = PallasScalar::from(value as u64);
    (PallasA::generator() * scalar).into_affine().into()
}

fn setup_trees() -> (
    CurveTreeOld<L>,
    FullCurveTree<L>,
    SelRerandParameters<PallasParameters, VestaParameters>,
) {
    let full_tree = CurveTreeOld::<L>::new_with_capacity(HEIGHT as usize, GENS_LENGTH);
    assert!(full_tree.height() == HEIGHT as usize);
    let params = full_tree.params().clone();
    let storage_tree = FullCurveTree::<L>::new_with_capacity(HEIGHT, GENS_LENGTH)
        .expect("Failed to create storage tree");
    assert!(storage_tree.height() == HEIGHT);

    // Compare roots
    let full_root = full_tree.root_node();
    let storage_root = storage_tree
        .root_node()
        .expect("Failed to get storage root");

    assert_roots_equal(&full_root, &storage_root, &format!("on empty trees"));

    (full_tree, storage_tree, params)
}

/// Compare two roots, printing debug info on mismatch since Root doesn't implement Debug
fn assert_roots_equal(
    full_root: &CurveTreeRoot<L>,
    storage_root: &CurveTreeRoot<L>,
    context: &str,
) {
    let full_root = full_root.decode().expect("Failed to decode full root");
    let storage_root = storage_root
        .decode()
        .expect("Failed to decode storage root");
    let roots_match = match (&full_root, &storage_root) {
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
        eprintln!("full tree root: {:#?}", full_root);
        eprintln!("storage tree root: {:#?}", storage_root);
        panic!("Roots differ: {}", context);
    }
}

/// Compare two paths by checking their structural equality
fn assert_paths_equal(
    full_path: &curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath<
        L,
        PallasParameters,
        VestaParameters,
    >,
    storage_path: &curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath<
        L,
        PallasParameters,
        VestaParameters,
    >,
    context: &str,
) {
    let paths_match = full_path.even_internal_nodes.len() == storage_path.even_internal_nodes.len()
        && full_path.odd_internal_nodes.len() == storage_path.odd_internal_nodes.len()
        && full_path
            .even_internal_nodes
            .iter()
            .zip(&storage_path.even_internal_nodes)
            .all(|(a, b)| {
                a.x_coord_children == b.x_coord_children
                    && a.child_node_to_randomize == b.child_node_to_randomize
            })
        && full_path
            .odd_internal_nodes
            .iter()
            .zip(&storage_path.odd_internal_nodes)
            .all(|(a, b)| {
                a.x_coord_children == b.x_coord_children
                    && a.child_node_to_randomize == b.child_node_to_randomize
            });

    if !paths_match {
        panic!("Paths differ: {}", context);
    }
}

/// Test insertion of leafs into `CurveTreeStorage` against the `FullCurveTree` implementation.
#[test]
fn test_inserts() {
    let (mut full_tree, mut storage_tree, _params) = setup_trees();

    // Test inserting a few leaves and comparing roots
    for i in 1..=5 {
        let leaf = create_test_leaf(i);

        // Insert into both trees
        full_tree.insert(leaf).unwrap();
        storage_tree.insert(leaf).unwrap();

        // Compare roots
        let full_root = full_tree.root_node();
        let storage_root = storage_tree
            .root_node()
            .expect("Failed to get storage root");

        assert_roots_equal(
            &full_root,
            &storage_root,
            &format!("after inserting leaf {}", i),
        );
    }
}

/// Test that both trees can grow beyond the initial L capacity
#[test]
fn test_growth_beyond_l() {
    let (mut full_tree, mut storage_tree, _params) = setup_trees();

    // Insert more leaves than L to test growth
    let num_leaves = L * 2 + 3; // 11 leaves when L=4

    for i in 1..=num_leaves {
        let leaf = create_test_leaf(i);

        // Insert into both trees
        full_tree.insert(leaf).unwrap();
        storage_tree.insert(leaf).unwrap();

        // Compare roots after each insertion
        let full_root = full_tree.root_node();
        let storage_root = storage_tree
            .root_node()
            .expect("Failed to get storage root");

        assert_roots_equal(
            &full_root,
            &storage_root,
            &format!("after inserting {} leaves", i),
        );
    }
}

/// Test updating existing leaves while adding new ones
#[test]
fn test_mixed_updates_and_inserts() {
    let (mut full_tree, mut storage_tree, _params) = setup_trees();

    // First, insert some initial leaves
    let initial_leaves = 6;
    for i in 1..=initial_leaves {
        let leaf = create_test_leaf(i);
        full_tree.insert(leaf).unwrap();
        storage_tree.insert(leaf).unwrap();
    }

    // Now mix updates and new insertions
    for round in 1..=3 {
        // Update an existing leaf
        let update_index = (round - 1) % initial_leaves;
        let new_value = create_test_leaf(100 + round);

        full_tree.update(new_value, update_index).unwrap();
        storage_tree
            .update(new_value, update_index as LeafIndex)
            .unwrap();

        // Insert a new leaf
        let new_leaf = create_test_leaf(200 + round);
        full_tree.insert(new_leaf).unwrap();
        storage_tree.insert(new_leaf).unwrap();

        // Compare roots after each round
        let full_root = full_tree.root_node();
        let storage_root = storage_tree
            .root_node()
            .expect("Failed to get storage root");

        assert_roots_equal(&full_root, &storage_root, &format!("after round {}", round));
    }
}

/// Test that paths to leaves are identical between implementations
#[test]
fn test_leaf_paths() {
    let (mut full_tree, mut storage_tree, _params) = setup_trees();

    // Insert several leaves
    let num_leaves = L + 2; // 6 leaves when L=4
    let mut leaf_values = Vec::new();

    for i in 1..=num_leaves {
        let leaf = create_test_leaf(i);
        leaf_values.push(leaf);

        full_tree.insert(leaf).unwrap();
        storage_tree.insert(leaf).unwrap();
    }

    // Compare paths for each leaf
    for (leaf_index, &_leaf_value) in leaf_values.iter().enumerate() {
        let full_path = full_tree.get_path_to_leaf_index(leaf_index).unwrap();
        let storage_path = storage_tree
            .get_path_to_leaf_index(leaf_index as LeafIndex)
            .unwrap();

        assert_paths_equal(
            &full_path,
            &storage_path,
            &format!("for leaf {}", leaf_index),
        );
    }
}

/// Test paths after updates to existing leaves
#[test]
fn test_paths_after_updates() {
    let (mut full_tree, mut storage_tree, _params) = setup_trees();

    // Insert initial leaves
    let num_leaves = 5;
    for i in 1..=num_leaves {
        let leaf = create_test_leaf(i);
        full_tree.insert(leaf).unwrap();
        storage_tree.insert(leaf).unwrap();
    }

    // Update some leaves
    for update_index in [0, 2, 4] {
        let new_value = create_test_leaf(300 + update_index);

        full_tree.update(new_value, update_index).unwrap();
        storage_tree
            .update(new_value, update_index as LeafIndex)
            .unwrap();

        // Check that all paths are still consistent
        for leaf_index in 0..num_leaves {
            let full_path = full_tree.get_path_to_leaf_index(leaf_index).unwrap();
            let storage_path = storage_tree
                .get_path_to_leaf_index(leaf_index as LeafIndex)
                .unwrap();

            assert_paths_equal(
                &full_path,
                &storage_path,
                &format!(
                    "for leaf {} after updating leaf {}",
                    leaf_index, update_index
                ),
            );
        }

        // Also check that roots are still the same
        let full_root = full_tree.root_node();
        let storage_root = storage_tree
            .root_node()
            .expect("Failed to get storage root");
        assert_roots_equal(
            &full_root,
            &storage_root,
            &format!("after updating leaf {}", update_index),
        );
    }
}

/// Test edge case: updating leaf at index 0
#[test]
fn test_update_first_leaf() {
    let (mut full_tree, mut storage_tree, _params) = setup_trees();

    // Insert a few leaves
    for i in 1..=3 {
        let leaf = create_test_leaf(i);
        full_tree.insert(leaf).unwrap();
        storage_tree.insert(leaf).unwrap();
    }

    // Update the first leaf (index 0)
    let new_first_leaf = create_test_leaf(999);
    full_tree.update(new_first_leaf, 0).unwrap();
    storage_tree.update(new_first_leaf, 0).unwrap();

    // Check roots match
    let full_root = full_tree.root_node();
    let storage_root = storage_tree
        .root_node()
        .expect("Failed to get storage root");
    assert_roots_equal(&full_root, &storage_root, "after updating first leaf");

    // Check paths for all leaves
    for leaf_index in 0..3 {
        let full_path = full_tree.get_path_to_leaf_index(leaf_index).unwrap();
        let storage_path = storage_tree
            .get_path_to_leaf_index(leaf_index as LeafIndex)
            .unwrap();

        assert_paths_equal(
            &full_path,
            &storage_path,
            &format!("for leaf {} after updating first leaf", leaf_index),
        );
    }
}

/// Test large tree growth
#[test]
fn test_large_tree_growth() {
    let (mut full_tree, mut storage_tree, _params) = setup_trees();

    // Insert a larger number of leaves to test scalability
    let num_leaves = L * 4; // 16 leaves when L=4

    for i in 1..=num_leaves {
        let leaf = create_test_leaf(i);

        full_tree.insert(leaf).unwrap();
        storage_tree.insert(leaf).unwrap();

        // Check roots every few insertions to catch issues early
        if i % L == 0 {
            let full_root = full_tree.root_node();
            let storage_root = storage_tree
                .root_node()
                .expect("Failed to get storage root");
            assert_roots_equal(&full_root, &storage_root, &format!("after {} leaves", i));
        }
    }

    // Final root check
    let full_root = full_tree.root_node();
    let storage_root = storage_tree
        .root_node()
        .expect("Failed to get storage root");
    assert_roots_equal(
        &full_root,
        &storage_root,
        &format!("final with {} leaves", num_leaves),
    );

    // Check a few random paths
    for &leaf_index in [0, L - 1, L, L + 1, num_leaves - 1].iter() {
        let full_path = full_tree.get_path_to_leaf_index(leaf_index).unwrap();
        let storage_path = storage_tree
            .get_path_to_leaf_index(leaf_index as LeafIndex)
            .unwrap();

        assert_paths_equal(
            &full_path,
            &storage_path,
            &format!("for leaf {} in large tree", leaf_index),
        );
    }
}

/// Test sequential updates to the same leaf
#[test]
fn test_sequential_leaf_updates() {
    let (mut full_tree, mut storage_tree, _params) = setup_trees();

    // Insert a few initial leaves
    for i in 1..=4 {
        let leaf = create_test_leaf(i);
        full_tree.insert(leaf).unwrap();
        storage_tree.insert(leaf).unwrap();
    }

    // Update the same leaf multiple times
    let target_index = 1;
    for update_round in 1..=5 {
        let new_value = create_test_leaf(1000 + update_round);

        full_tree.update(new_value, target_index).unwrap();
        storage_tree
            .update(new_value, target_index as LeafIndex)
            .unwrap();

        // Check roots after each update
        let full_root = full_tree.root_node();
        let storage_root = storage_tree
            .root_node()
            .expect("Failed to get storage root");
        assert_roots_equal(
            &full_root,
            &storage_root,
            &format!(
                "after update round {} of leaf {}",
                update_round, target_index
            ),
        );

        // Check path for the updated leaf
        let full_path = full_tree.get_path_to_leaf_index(target_index).unwrap();
        let storage_path = storage_tree
            .get_path_to_leaf_index(target_index as LeafIndex)
            .unwrap();
        assert_paths_equal(
            &full_path,
            &storage_path,
            &format!(
                "path for leaf {} after update round {}",
                target_index, update_round
            ),
        );
    }
}

/// Test stress scenario with many updates and insertions
#[test]
fn test_stress_updates_and_insertions() {
    let (mut full_tree, mut storage_tree, _params) = setup_trees();

    // Insert initial batch of leaves
    let initial_batch = L + 3; // 7 leaves when L=4
    for i in 1..=initial_batch {
        let leaf = create_test_leaf(i);
        full_tree.insert(leaf).unwrap();
        storage_tree.insert(leaf).unwrap();
    }

    // Perform mixed operations
    for cycle in 1..=3 {
        // Insert new leaves
        for j in 1..=2 {
            let leaf = create_test_leaf(1000 * cycle + j);
            full_tree.insert(leaf).unwrap();
            storage_tree.insert(leaf).unwrap();
        }

        // Update existing leaves (update multiple leaves per cycle)
        let cycle_usize = cycle as usize;
        for update_idx in [
            0,
            cycle_usize % initial_batch,
            (cycle_usize * 2) % initial_batch,
        ] {
            let new_value = create_test_leaf(2000 * cycle + update_idx);
            full_tree.update(new_value, update_idx).unwrap();
            storage_tree
                .update(new_value, update_idx as LeafIndex)
                .unwrap();
        }

        // Verify consistency after each cycle
        let full_root = full_tree.root_node();
        let storage_root = storage_tree
            .root_node()
            .expect("Failed to get storage root");
        assert_roots_equal(
            &full_root,
            &storage_root,
            &format!("after stress cycle {}", cycle),
        );
    }
}
