def find_triplets(n):
    if n < 3:
        return []
    
    triplets = [(1, 2, 3)]
    
    for k in range(4, n + 1):
        found = False
        # Case 1: Search for a, b in {1, 2, 3} for k=4
        if k == 4:
            for a in range(1, 4):
                for b in range(a + 1, 4):
                    # We need exactly one. Let's just pick (1, 2, 4)
                    triplets.append((1, 2, 4))
                    found = True
                    break
                if found: break
        else:
            # Case 2: k > 4
            # (a, b, k) where b > 3
            # Condition: (-, a, b) or (a, -, b) is in the list
            # And (a, b, l) is not in the list for 4 <= l < k
            
            # We need to find a, b such that:
            # 1. 1 <= a < b < k
            # 2. b > 3
            # 3. There exists some x such that (x, a, b) or (a, x, b) is in the current triplets list
            # 4. No triplet (a, b, l) exists in triplets for 4 <= l < k
            
            potential_candidates = []
            for a in range(1, k):
                for b in range(a + 1, k):
                    if b > 3:
                        # Check condition 3: (x, a, b) or (a, x, b) exists
                        exists_prev = any((t[1] == a and t[2] == b) or (t[0] == a and t[2] == b) for t in triplets)
                        
                        if exists_prev:
                            # Check condition 4: (a, b, l) not in list for 4 <= l < k
                            # In our logic, triplets only contains one for each k.
                            # So we check if any triplet in triplets[1:] (which are for l=4..k-1) has (a, b, _)
                            already_used = any(t[0] == a and t[1] == b for t in triplets[1:])
                            
                            if not already_used:
                                potential_candidates.append((a, b, k))
            
            if potential_candidates:
                # Pick the first valid one to maintain "exactly one"
                triplets.append(potential_candidates[0])
            else:
                # If no such b > 3 exists (which might happen if we don't have enough k-1 triplets), 
                # check if there's a fallback? The prompt says "if b > 3 iff ...". 
                # This implies if b <= 3, the condition doesn't apply.
                # However, for k > 4, if we must have exactly one triplet (a, b, k), 
                # and the condition only constrains b > 3, we can pick b <= 3.
                for a in range(1, 4):
                    for b in range(a + 1, 4):
                        # check condition 4
                        already_used = any(t[0] == a and t[1] == b for t in triplets[1:])
                        if not already_used:
                            triplets.append((a, b, k))
                            found = True
                            break
                    if found: break

    return triplets

print(f"n=6: {find_triplets(6)}")
print(f"n=10: {find_triplets(10)}")