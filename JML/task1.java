// Task 1
//  PART (B) 
// Write assignable clauses where appropriate. = DONE(An assignable clause specifies which variables may be modified by a method; all other variables should remain unchanged)
// • Write class invariants. = DONE
// • Write a loop invariant, decreases clause, and assignable clause for the loop in method add. = DONE
// • Add JML modifiers (spec_public, pure,...) where necessary. = DONE


public class HashTable {
    
	// Open addressing Hashtable with linear probing as collision resolution.
	
	/*@ 
	invariant 
	(size < capacity)? return && size=size+1 && obj=h[i] :return 	
	 @*/ 

	/*@ invariant h.length=size @*/ 

	public /*@ non_null @*/ Object[] h;
	
	public int size; 
	
	/*@ invariant capacity >=1 @*/ 
	public int capacity;
    
    /*@ invariant 0 >= size && size <= capacity; @*/ 

    /*@ invariant capacity=h.length @*/ 

	HashTable (int capacity) {
		  /*@ assignable h,capacity,size @*/ 
		h = new Object[capacity]; 
		this.capacity = capacity;
		size = 0;
	}
		
	public int hash_function (int val) {
	
        int result = 0;
		
		if (val >= 0)
		   result = val % capacity;
		else {result = (val * -1) % capacity;}
		
		return result;
	}
		
	public /*@ pure @*/ void add (Object u, int key) {
    
	/*@ assignable size, h[i] @*/ 
		
	    if (size < capacity) {
     
    
	    int i = hash_function(key);

		if (h[i] == null) {
		    h[i] = u;
			size++;
			return;
			}
		else {		
			int j = 0;

			//LOOP INVARIANT
			/*
			@loop_invariant \result= (\forall int i; i>=0 && i<\index; i=i+1);
			@decreases capacity -\index;
			@assignable \strictly_nothing
			@*/
			
			while (h[i] != null && j < capacity)
		    {
             if (i == capacity-1) i = 0;
             else {i++;}
             
             j++;
		    }
			
			h[i] = u;
			size++;
			return;			
		  }	

        } else {
               return;
               }	
	}   
	
}
