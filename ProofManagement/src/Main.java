import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Properties;
import java.util.zip.ZipException;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import consistencyChecking.ConsistencyChecker;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.IPersistablePO;
import de.uka.ilkd.key.proof.init.IPersistablePO.LoadedPOContainer;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.IntermediatePresentationProofFileParser;
import de.uka.ilkd.key.proof.io.consistency.DiskFileRepo;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.proof.io.intermediate.BranchNodeIntermediate;
import de.uka.ilkd.key.util.ProgressMonitor;
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
                if (ConsistencyChecker.consistent(proofFiles, ph.getFileRepo())) {
                    System.out.println("Consistent!");
                } else {
                    System.out.println("Inconsistent!");
                }
                return;
            }
            System.out.println(USAGE);
        }

        try {
            loadFile(PATH);
        }
        catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        catch (ProofInputException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }

    static void loadFile(String path) throws IOException, ProofInputException {
        Profile profile = AbstractProfile.getDefaultProfile();
        FileRepo fileRepo;
        fileRepo = new DiskFileRepo("testProof");
        fileRepo.setBaseDir(Paths.get(path));
        ProgressMonitor control = ProgressMonitor.Empty.getInstance();

        Path pa = Paths.get(path);
        KeYUserProblemFile keyFile = new KeYUserProblemFile(pa.getFileName().toString(), pa.toFile(), fileRepo,
                control, profile, false);

        ProblemInitializer pi = new ProblemInitializer(control, new Services(profile),
                new DefaultUserInterfaceControl());
        pi.setFileRepo(fileRepo);

        InitConfig initConfig = pi.prepare(keyFile);
        initConfig.setFileRepo(fileRepo);

        //        String chooseContract = keyFile.chooseContract();
        String proofObligation = keyFile.getProofObligation();

        //        Contract contract = initConfig.getServices().getSpecificationRepository().getContractByName(chooseContract);

        LoadedPOContainer poContainer;

        // Load proof obligation settings
        final Properties properties = new Properties();
        properties.load(new ByteArrayInputStream(proofObligation.getBytes()));
        properties.setProperty(IPersistablePO.PROPERTY_FILENAME, path);
        //        if (poPropertiesToForce != null) {
        //            properties.putAll(poPropertiesToForce);
        //        }
        //        String poClass = properties.getProperty(IPersistablePO.PROPERTY_CLASS);



        //        try {
        //            // Try to instantiate proof obligation by calling static method: public static LoadedPOContainer loadFrom(InitConfig initConfig, Properties properties) throws IOException
        //            Class<?> poClassInstance = ClassLoaderUtil.getClassforName(poClass);
        //            Method loadMethod = poClassInstance.getMethod("loadFrom", InitConfig.class, Properties.class);
        //             poContainer = (LoadedPOContainer)loadMethod.invoke(null, initConfig, properties);
        //             FunctionalOperationContractPO.loadFrom(initConfig, properties);
        //        }
        //        catch (Exception e) {
        //            throw new IOException("Can't call static factory method \"loadFrom\" on class \"" + poClass + "\".", e);
        //        }
        //        LoadedPOContainer poContainer = new LoadedPOContainer(contract.createProofObl(initConfig), 0);

        poContainer = FunctionalOperationContractPO.loadFrom(initConfig, properties);

        ProofAggregate proofList =
                pi.startProver(initConfig, poContainer.getProofOblInput());

        for (Proof p : proofList.getProofs()) {
            // register proof
            initConfig.getServices().getSpecificationRepository().registerProof(poContainer.getProofOblInput(), p);
        }

        Proof proof = proofList.getProof(poContainer.getProofNum());

        IntermediatePresentationProofFileParser parser = null;
        //        IntermediatePresentationProofFileParser.Result parserResult = null;



        Services srv = new Services(profile);

        //        final String ossStatus =
        //                (String) proof.getSettings().getStrategySettings()
        //                        .getActiveStrategyProperties()
        //                        .get(StrategyProperties.OSS_OPTIONS_KEY);
        //

        parser = new IntermediatePresentationProofFileParser(proof);
        pi.tryReadProof(parser, keyFile);
        BranchNodeIntermediate result = parser.getParsedResult();
        //        parserResult = ((IntermediatePresentationProofFileParser) parser). getResult().;
    }

}
