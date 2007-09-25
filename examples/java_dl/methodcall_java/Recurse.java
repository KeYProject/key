public class Recurse {

    int recurse(boolean clear) {
	int x = 1;
	if ( clear ) {
	    x=0;
	} else {
	    recurse(true);
	}
	return x;
    }

}
