// TASK 3  
// modifiers (spec_public,pure) = DONE
// method contracts(pre post conditions) = DONE 
// class invariants= DONE
// loop invariants= NO ANY

public class Wallet {

    // class invariants
    /*@ 
    invariant pin.length= 4;
    invariant balance >=0;
    @*/ 


    final/*@spec_public @*/  int MAX_BALANCE=100000;
    int  /*@spec_public non_null @*/ balance; 
    byte[] /*@spec_public non_null @*/ pin; //must contain 4 digits
     
    Wallet(int b, byte[] p) 
    {
        balance = b; 
        pin = p;
    }

  //contracts (pre+ post conditions)

    /*@ 
    requires amount>=0; 
	ensures balance;
    signals (PurseException e) amount > balance &&
	                                          balance == \old(balance) ; 
     @*/ 

    int debit(int amount) throws PurseException 
    {
        if(amount <= balance) 
        { 
            balance -= amount; 
            return balance;
        }
        else{
            throw new PurseException("overdrawn by "+amount);
            }
    }
            }