//WizardWallet
#include "Wallet.h"

static int galleon;
static int sickle;
static int knut;
  
/*@
	assigns \nothing;
	ensures \result == amount / 493;
*/
static int toGalleons(int amount) {
	return amount / 493;
}
 
/*@
	assigns \nothing;
	ensures \result == (amount % 493) / 29;
*/
static int toSickles(int amount) {
	return (amount % 493) / 29;
}

/*@
	assigns \nothing;
	ensures \result == (amount % 493) % 29;
*/
static int toKnuts(int amount) {
	return (amount % 493) % 29;
}

/* Seventeen silver Sickles to a Galleon and twenty-nine Knuts to a Sickle.
Therefore 1 Galleon = 17 Sickles = 493 Knuts. */
    
/* Pay money to someone. The price is specified in Knuts. */
/*@
	requires count == 493 * galleon + 29 * sickle + knut;
	assigns galleon, sickle, knut, count;
	ensures count == 493 * galleon + 29 * sickle + knut;
*/
void pay(int price) {
	galleon = galleon - toGalleons(price);
	sickle = sickle - toSickles(price);
	knut = knut - toKnuts(price);
	//@ ghost count -= price;
}

/* Performs the Doubling Charm. This charm doubles the amount of money in
the wallet. */
/*@ 
	requires count == 493 * galleon + 29 * sickle + knut;
    assigns galleon, sickle, knut, count;
	ensures count == 493 * galleon + 29 * sickle + knut;
*/
void doublingCharm() {
	knut = knut * 2;
	int knutToSickles = knut / 29;
	knut = knut % 29;
	sickle = sickle * 2 + knutToSickles;
	int sicklesToGalleons = sickle / 17;
	sickle = sickle % 17;
	galleon = galleon * 2 + sicklesToGalleons;
	//@ ghost count *= 2;
}