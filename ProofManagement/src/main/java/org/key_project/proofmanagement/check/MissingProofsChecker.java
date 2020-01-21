package org.key_project.proofmanagement.check;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.java.JavaSourceElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.proof.io.consistency.TrivialFileRepo;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.SLEnvInput;
import de.uka.ilkd.key.util.ProgressMonitor;
import org.key_project.proofmanagement.io.ProofBundleHandler;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.stream.Collectors;

/**
 * Checks that there exists a proof for every contract.
 * Has to be combined with other checkers to ensure that the proofs are actually consistent
 * as well as correct.
 */
public class MissingProofsChecker implements Checker {

    private ProofBundleHandler pbh;

    @Override
    public CheckerData check(List<Path> proofFiles, CheckerData data) {

        try {
            // TODO: implement case with no proof file

            // load all contracts from source files
            pbh = data.getPbh();
            Path base = pbh.getDir();
            File src = base.resolve(Paths.get("src")).toFile();
            List<File> cp = null;
            if (!pbh.getClasspathFiles().isEmpty()) {
                cp = pbh.getClasspathFiles().stream()
                                            .map(Path::toFile)
                                            .collect(Collectors.toList());
            }
            File bcp = null;
            if (!pbh.getBootclasspathFiles().isEmpty()) {
                base.resolve(Paths.get("bcp")).toFile();
            }
            Profile profile = AbstractProfile.getDefaultProfile();

            SLEnvInput slenv = new SLEnvInput(src.toString(), cp, bcp, profile, null);

            ProgressMonitor control = ProgressMonitor.Empty.getInstance();
            ProblemInitializer pi = new ProblemInitializer(control, new Services(profile),
                new DefaultUserInterfaceControl());
            pi.setFileRepo(new TrivialFileRepo());
            InitConfig ic = pi.prepare(slenv);
            SpecificationRepository specRepo = ic.getServices().getSpecificationRepository();
            Set<Contract> contracts = specRepo.getAllContracts().toSet();
            Set<Contract> copy = new HashSet<>(contracts);

            // load proof files
            Set<Proof> foundProofs = loadProofs(proofFiles);

            List<CheckerData.ProofLine> lines = new ArrayList<>();

            // compare: Is there a proof for every contract?
            for (Proof p : foundProofs) {
                SpecificationRepository sr = p.getServices().getSpecificationRepository();
                ContractPO cpo = sr.getPOForProof(p);
                ContractPO cpo2 = sr.getContractPOForProof(p);
                Contract foundContract = cpo.getContract();

                if (foundContract == null) {
                    System.err.println("Missing contract for proof: " + p.name());
                    // TODO: should not happen
                } else {
                    //System.out.println("Contract found for proof: " + p.name());

                    // search for matching contract and delete it (this contract has a proof)
                    Contract rem = null;
                    for (Contract contr : copy) {
                        if (contr.getName().equals(foundContract.getName())) {
                            rem = contr;
                            CheckerData.ProofLine line = new CheckerData.ProofLine();
                            line.contract = contr;
                            line.proof = p;
                            line.proofFile = p.getProofFile().toPath();
                            lines.add(line);
                            // TODO: how to get source file?
                            Type type = contr.getTarget().getContainerType().getJavaType();
                            if (type instanceof JavaSourceElement) {
                                JavaSourceElement jse = (JavaSourceElement) type;
                                line.sourceFile = jse.getPositionInfo().getURI().toURL();
                                String str = line.sourceFile.toString();
                                line.shortSrc = str.substring(str.lastIndexOf('/') + 1);
                            }
                            break;
                        }
                    }
                    if (rem != null) {
                        copy.remove(rem);
                    }
                }
            }

            boolean consistent = true;
            for (Contract c : copy) {
                // TODO: currently contracts from inside java.* package are filtered/ignored
                if (!c.getName().startsWith("java.")) {
                    System.out.println("Error! Missing proof for contract " + c.getName());
                    data.setConsistent(false); // at least one contract is left unproven!
                }
            }
            data.setProofLines(lines);

        } catch (ProofInputException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        }

        return data;
    }

    public Set<Proof> loadProofs(List<Path> proofFiles) throws ProofInputException, IOException {
        Set<Proof> allProofs = new HashSet<>();
        // load each proof file
        for (Path path : proofFiles) {
            Proof[] proofs = loadProofFile(path);
            // add each proof to set of all proofs
            for (Proof proof : proofs) {
                allProofs.add(proof);
            }
        }
        return allProofs;
    }

    public Proof[] loadProofFile(Path path) throws ProofInputException, IOException {
        Profile profile = AbstractProfile.getDefaultProfile();

        FileRepo fileRepo = new TrivialFileRepo();
        fileRepo.setBaseDir(path);

        ProgressMonitor control = ProgressMonitor.Empty.getInstance();

        KeYUserProblemFile keyFile = new KeYUserProblemFile(path.getFileName().toString(),
            path.toFile(), fileRepo, control, profile, false);

        ProblemInitializer pi = new ProblemInitializer(control, new Services(profile),
            new DefaultUserInterfaceControl());
        pi.setFileRepo(fileRepo);

        InitConfig initConfig = pi.prepare(keyFile);
        initConfig.setFileRepo(fileRepo);

        String proofObligation = keyFile.getProofObligation();

        // Load proof obligation settings
        final Properties properties = new Properties();
        properties.load(new ByteArrayInputStream(proofObligation.getBytes()));
        properties.setProperty(IPersistablePO.PROPERTY_FILENAME, path.toString());

        IPersistablePO.LoadedPOContainer poContainer = FunctionalOperationContractPO.loadFrom(initConfig, properties);

        ProofAggregate proofList = pi.startProver(initConfig, poContainer.getProofOblInput());
        for (Proof p : proofList.getProofs()) {
            // register proof
            initConfig.getServices().getSpecificationRepository()
                .registerProof(poContainer.getProofOblInput(), p);
            initConfig.getFileRepo().registerProof(p);
        }

        return proofList.getProofs();
    }
}
