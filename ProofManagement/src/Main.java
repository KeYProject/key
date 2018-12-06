import consistencyChecking.ConsistencyChecker;

public class Main {

    private static final String USAGE = "Usage: TODO";
    public static void main(String[] args) {

        if (args.length != 0) {

            if (args[0].equals("check") && (args.length == 2)) {
                ConsistencyChecker.consistent(args[1]);
                return;
            }

        }
        System.out.println(USAGE);
    }

}
