import consistencyChecking.ConsistencyChecker;

public class Main {

    private static final String USAGE = "Usage: TODO";
    public static void main(String[] args) {
        
        System.out.println("Hallo HacKeYthon!");
        if (args.length != 0) {

            if (args[0].equals("check") && (args.length == 2)) {
                if (ConsistencyChecker.consistent(args[1])) {
                    System.out.println("Consistent!");
                } else {
                    System.out.println("Inconsistent!");
                }
                return;
            }
            System.out.println(USAGE);
        }
    }
}
