import random

def generate_valid_triplets(n):
    if n < 3:
        return []
    
    triplets = [(1, 2, 3)]
    
    for k in range(4, n + 1):
        possible_a_b = []
        if k == 4:
            # (a, b, 4) where a, b in {1, 2, 3} and a < b
            for a in range(1, 4):
                for b in range(a + 1, 4):
                    possible_a_b.append((a, b))
        else:
            # For k > 4, (a, b, k) with 1 <= a < b < k
            for a in range(1, k):
                for b in range(a + 1, k):
                    # Condition: b > 3 iff (- , a, b) or (a, -, b) is in triplets for some l < k
                    # AND (a, b, l) is not in triplets for 4 <= l < k
                    
                    # Condition 2: (a, b, l) not in triplets for 4 <= l < k
                    exists_earlier = False
                    for (x, y, z) in triplets:
                        if z >= 4 and x == a and y == b:
                            exists_earlier = True
                            break
                    if exists_earlier:
                        continue
                    
                    # Condition 1: b > 3 iff there exists a triplet (x, y, z) in triplets 
                    # such that z < k and ((x=a and y=b) is false, since we checked that above)
                    # wait, the condition is b > 3 iff (-, a, b) or (a, -, b) in list.
                    # This means there is some z < k such that (x, a, b) or (a, x, b) is in the list.
                    
                    found_dependency = False
                    for (x, y, z) in triplets:
                        if (x == a and y == b) or (x == a and z == b) or (y == a and z == b):
                           # Note: The triplet is (x, y, z) with x < y < z. 
                           # We are looking for something that contains a and b as members.
                           # Specifically (- , a, b) means (x, a, b) where x < a.
                           # (a, -, b) means (a, x, b) where a < x < b.
                           if (y == a and z == b) or (x == a and z == b):
                               found_dependency = True
                               break
                    
                    if (b > 3) == found_dependency:
                        possible_a_b.append((a, b))
        
        if not possible_a_b:
            # If no valid pair exists, this branch is dead. In a real generator we'd backtrack.
            # But let's see if we can pick one.
            return None
            
        a, b = random.choice(possible_a_b)
        triplets.append((a, b, k))
        
    return triplets

# Test for n=6
for _ in range(5):
    print(generate_valid_triplets(6))
