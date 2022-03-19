// TASK 2  
// modifiers (spec_public,pure) = DONE
// method contracts(pre post conditions) = DONE 
// class invariants= DONE
// loop invariants= DONE

public class BinarySearch {

    // class invariants
    /*@ invariant size >=0 && size= numbers.length @*/ 

    private /*@spec_public non_null @*/  int[] numbers; //array must be sorted
    private /*@spec_public @*/ int size;    

    //contracts (pre+ post conditions)

    /*@ 
    requires (\forall int i, j; 0 <= i & i < j & j < a.length; a[i] <= a[j]);
    requires query !=null;
	ensures \result== index; 
    ensures \result == -1;
     @*/ 

    private /*@ pure @*/ int search(int query) 
    {
        int leftIndex = 0;
        int rightIndex = size;

        //LOOP INVARIANT
	        /*
            @maintaining (\exists int j; 0<=j && j<leftIndex;numbers [j] <query);
			@maintaining 0 <= leftIndex && leftIndex<= rightIndex;
			@decrease rightIndex -leftIndex;
			@assignable \strictly_nothing;
			@*/

        while (leftIndex <= rightIndex) 
        {
            int index = leftIndex+((rightIndex-leftIndex)/2);
            if (numbers[index] < query)
             {
                 leftIndex = index + 1;
                 } 
                 else if (numbers[index] > query) 
                 {
                     rightIndex = index -1;
                     }
                     else 
                     {  
                         return index;
                         }
                         }
                         return -1;
                         }
                         }