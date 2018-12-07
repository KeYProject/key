import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.zip.ZipException;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import consistencyChecking.SettingsChecker;
import io.PackageHandler;

public class Main {

    final static String PATH = "/home/wolfram/Schreibtisch/Cycle(Cycle__m()).JML operation contract.0.proof";

    private static final String USAGE = "Usage: TODO";
    public static void main(String[] args) {
        System.out.println("Hallo HacKeYthon!");
        if (args.length != 0) {
            if (args[0].equals("check") && (args.length == 2)) {
                PackageHandler ph = new PackageHandler(Paths.get(args[1]));
                ImmutableList<Path> proofFiles = ImmutableSLList.nil();
                try {
                    proofFiles = proofFiles.append(ph.getProofFiles());
                }
                catch (ZipException e) {
                    // TODO Auto-generated catch block
                    e.printStackTrace();
                }
                catch (IOException e) {
                    // TODO Auto-generated catch block
                    e.printStackTrace();
                }
                if (new SettingsChecker().check(proofFiles)) {
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
