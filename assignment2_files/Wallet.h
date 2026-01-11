//interface Wallet 
//@ ghost int count;
//@ global invariant I: count >= 0;

/*@
    requires count>=price;
    ensures count == \old(count) - price;
*/
void pay(int price);

//@ ensures count == \old(count) * 2;
void doublingCharm();
