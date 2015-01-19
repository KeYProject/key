// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.lemmatagenerator;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProblemInitializer.ProblemInitializerListener;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;
import de.uka.ilkd.key.util.ProgressMonitor;

public class EnvironmentCreator  {
        
        private KeYUserProblemFile keyFile;
        
        public KeYUserProblemFile getKeyFile() {
                if(keyFile == null){
                        throw new IllegalStateException("You must call the method create before");
                }
                return keyFile;
        }
        
        
        public ProofEnvironment create(String pathForDummyFile,ProgressMonitor monitor,
                          ProblemInitializerListener listener, Profile profile) throws IOException,
        ProofInputException {
                File dummyFile = createDummyKeYFile(pathForDummyFile);
                keyFile = new KeYUserProblemFile(
                                dummyFile.getName(), dummyFile, null, profile);

                ProblemInitializer pi = new ProblemInitializer(monitor, 
                                new Services(profile),
                                listener );
               
                return new ProofEnvironment(pi.prepare(keyFile));
        }

        private File createDummyKeYFile(String pathForDummyFile) throws IOException {
                File file = new File(pathForDummyFile + File.separator
                                + "lemmataGenDummy.key");
                // see bug #1426
                // file.deleteOnExit();
                if(!file.exists()) {
                    String s = "\\problem{true}";
                    FileWriter writer = new FileWriter(file);
                    writer.write(s);
                    writer.close();
                }
                return file;
        }
}