public class PayCard {
    int limit=1000;
    int unsuccessfulOperations;
    int id;
    int balance=0;

    public PayCard(int limit) {
        balance = 0;
        unsuccessfulOperations=0;
        this.limit=limit;
    }

    public PayCard() {
	balance=0;
        unsuccessfulOperations=0;
    }

    /* @preconditions amount>0
     * @postconditions balance>=balance@pre
     */
   public void charge(int amount) {
        if (this.balance+amount>=this.limit) {
            this.unsuccessfulOperations++;
        } else {
            this.balance=this.balance+amount;
        }
    }

    // @postconditions result=balance or unsuccessfulOperations>3
    public int available() {
	if (unsuccessfulOperations<=3) {
	    return this.balance;
        }
        return 0;
    }


    public String infoCardMsg() {
        return (" Current balance on card is " + balance);
    }
}
