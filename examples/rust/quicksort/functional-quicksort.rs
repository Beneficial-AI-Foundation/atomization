// src/functional_quicksort.rs

/// A purely functional implementation of quicksort that returns a new sorted vector
/// instead of sorting in place. This version takes a comparison function.
pub fn quicksort_functional<T, F>(items: &[T], compare: F) -> Vec<T> 
where 
    T: Clone,
    F: Fn(&T, &T) -> std::cmp::Ordering + Copy,
{
    if items.len() <= 1 {
        return items.to_vec();
    }
    
    // Take the first element as the pivot
    let pivot = &items[0];
    
    // Partition the rest of the items
    let rest = &items[1..];
    
    // Items less than the pivot
    let lesser: Vec<T> = rest
        .iter()
        .filter(|item| compare(item, pivot) == std::cmp::Ordering::Less)
        .cloned()
        .collect();
    
    // Items equal to the pivot
    let equal: Vec<T> = rest
        .iter()
        .filter(|item| compare(item, pivot) == std::cmp::Ordering::Equal)
        .cloned()
        .collect();
    
    // Items greater than the pivot
    let greater: Vec<T> = rest
        .iter()
        .filter(|item| compare(item, pivot) == std::cmp::Ordering::Greater)
        .cloned()
        .collect();
    
    // Recursively sort the partitions and concatenate the results
    let mut result = quicksort_functional(&lesser, compare);
    result.push(pivot.clone());
    result.extend(equal);
    result.extend(quicksort_functional(&greater, compare));
    
    result
}

/// A version of quicksort_functional with default ordering for types that implement Ord
pub fn quicksort_functional_ord<T>(items: &[T]) -> Vec<T> 
where 
    T: Ord + Clone,
{
    quicksort_functional(items, |a, b| a.cmp(b))
}

/// Transform a vector of data using a series of functional operations
pub fn transform_and_sort<T, U, F, G>(
    data: &[T],
    transform: F,
    compare: G,
) -> Vec<U>
where
    T: Clone,
    U: Clone,
    F: Fn(&T) -> U,
    G: Fn(&U, &U) -> std::cmp::Ordering + Copy,
{
    // Transform the data first
    let transformed: Vec<U> = data.iter().map(transform).collect();
    
    // Then sort using our functional quicksort
    quicksort_functional(&transformed, compare)
}

// Example of a complex data operation pipeline using our functional quicksort
pub fn word_frequency_analysis(text: &str) -> Vec<(String, usize)> {
    // Split the text into words
    let words: Vec<String> = text
        .split_whitespace()
        .map(|word| word.trim_matches(|c: char| !c.is_alphabetic()).to_lowercase())
        .filter(|word| !word.is_empty())
        .collect();
    
    // Count word frequencies (using a functional fold operation)
    let mut word_counts: Vec<(String, usize)> = Vec::new();
    
    for word in words {
        match word_counts.iter().position(|(w, _)| w == &word) {
            Some(index) => {
                // Create a new vector with the updated count
                let (_, count) = word_counts[index];
                word_counts = word_counts
                    .iter()
                    .enumerate()
                    .map(|(i, (w, c))| 
                        if i == index { 
                            (w.clone(), c + 1) 
                        } else { 
                            (w.clone(), *c) 
                        }
                    )
                    .collect();
            },
            None => word_counts.push((word, 1)),
        }
    }
    
    // Sort by frequency (highest first)
    quicksort_functional(&word_counts, |a, b| b.1.cmp(&a.1))
}
