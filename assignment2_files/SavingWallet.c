//SavingWallet
#include "Wallet.h"

static int money;
static int saving;

//@ global invariant I: money + saving >= 0;

/*@ 
	requires count == money + saving;
	assigns money, saving, count;
	ensures count == money + saving;
*/
void pay(int price) {
	money = money - price;
	int new_save = price * 0.25;
	
	if (money >= new_save) {
		money = money - new_save;
		saving = saving + new_save;                     
	}
    //@ ghost count -= price;
}