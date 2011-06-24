// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui.smt;

import java.util.List;

import javax.swing.table.DefaultTableModel;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;

import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.smt.SolverType;

public class SettingsModel{


        public final static int OPTIONCOL=1; 
        public final static int width []= {10,-1,30};
        public final static TableSeperator seperator = new TableSeperator();


  
        private final SMTSettings originalSettings;
        private final SMTSettings temporarySettings;
    



        private DefaultTreeModel contentModel;
        private ContentItem defaultItem = null;
        
      

        public final static String PROGRESS_MODE_USER = "Progress dialog remains open after executing solvers.";
        public final static String PROGRESS_MODE_CLOSE = "Close progress dialog after all solvers have finished.";
        public final static String PROGRESS_MODE_CLOSE_FIRST = "Close progress dialog after the first solver has finished.";

        public String getProgressMode(int index) {
                switch (index) {
                case ProofIndependentSettings.PROGRESS_MODE_USER:
                        return PROGRESS_MODE_USER;
                case ProofIndependentSettings.PROGRESS_MODE_CLOSE:
                        return PROGRESS_MODE_CLOSE;
                case ProofIndependentSettings.PROGRESS_MODE_CLOSE_FIRST:
                        return PROGRESS_MODE_CLOSE_FIRST;
                }
                return "";
        }

        public SettingsModel(      
                        ProofDependentSettings pdSettings,
                        ProofIndependentSettings piSettings, Proof proof) {
                originalSettings = new SMTSettings(pdSettings, piSettings, proof);
                temporarySettings = new SMTSettings(pdSettings.clone(), piSettings.clone(),proof);
               
                createContentModel();
        }


        public void applyChanges() {
 
                originalSettings.copy(temporarySettings);
                originalSettings.fireSettingsChanged();
        }

        private void createContentModel() {
                DefaultTableModel def = buildModel("Options",
                                getGeneralOptionsData());
                defaultItem = new ContentItem("Options", def);
                DefaultMutableTreeNode root = new DefaultMutableTreeNode();
                root.setUserObject(defaultItem);

                DefaultMutableTreeNode solverOptions = new DefaultMutableTreeNode();
                solverOptions.setUserObject(new ContentItem("Solvers", def));
                for (SolverType type : temporarySettings.getPiSettings()
                                .getSupportedSolvers()) {
                        DefaultMutableTreeNode solver = new DefaultMutableTreeNode();
                        solver.setUserObject(new ContentItem(type.getName(),
                                        buildModel(type.getName(),
                                                        getSolverData(type))));
                        solverOptions.add(solver);
                }

                DefaultMutableTreeNode hierarchyOptions = new DefaultMutableTreeNode();
                hierarchyOptions.setUserObject(new ContentItem("Translation",
                                buildModel("Translation",
                                                getTranslationOptionData())));

                DefaultMutableTreeNode tacletOptions = new DefaultMutableTreeNode();
                tacletOptions.setUserObject(new ContentItem("Taclets",
                                buildModel("Taclets", getTacletOptionsData())));

                DefaultMutableTreeNode tacletSelection = new DefaultMutableTreeNode();
                tacletSelection.setUserObject(new ContentItem("Selection",
                                (new TacletTranslationSelection(
                                                temporarySettings))
                                                .getSelectionTree()));
                tacletOptions.add(tacletSelection);

                root.add(solverOptions);
                root.add(hierarchyOptions);
                root.add(tacletOptions);

                contentModel = new DefaultTreeModel(root);
                // setModel(model);

        }
        
        private DefaultTableModel buildModel(String title, Object[] data) {
                DefaultTableModel model = new DefaultTableModel();

                model = new DefaultTableModel();
                model.addColumn("");
                model.addColumn(title);
                model.addColumn("");

                Object[] sep = { seperator, seperator, seperator };
                model.addRow(sep);
                for (int i = 0; i < data.length; i++) {
                        Object[] dat = { sep[0], data[i], sep[0] };
                        model.addRow(dat);
                        model.addRow(sep);

                }


                return model;
        }
        
        public DefaultTreeModel getContentModel() {
                return contentModel;
        }
        
        public void storeAsDefault(){
                ProofSettings.DEFAULT_SETTINGS.getSMTSettings().copy(temporarySettings.getPdSettings());
        }

        private TableComponent[] getTranslationOptionData() {
                TableComponent data[] = { new TableCheckBox() {
                        public boolean prepareValues() {
                                setTitle("Use explicit type hierarchy.");
                                setSelected(temporarySettings.getPdSettings().useExplicitTypeHierarchy);
                                return true;
                        }

                        @Override
                        public void eventChange() {
                                temporarySettings.getPdSettings().useExplicitTypeHierarchy = isSelected();
                        }

                        @Override
                        public String getInfo() {
                                return "If this option is selected, the transitive inheritance between classes is modeled by "
                                                + "assumptions.\n\n"
                                                + "Example: Let A, B and C  be classes such that C extends B and B extends A.\n"
                                                + "If the option is not selected, the following assumptions are added:\n"
                                                + "\\forall x; (type_of_C(x)->type_of_B(x))\n"
                                                + "\\forall x; (type_of_B(x)->type_of_A(x))\n"
                                                + "If the option is selected, the following assumption is additionally added to the assumptions above:\n"
                                                + "\\forall x; (type_of_C(x)->type_of_A(x))\n";
                        }
                }, new TableCheckBox() {
                        public boolean prepareValues() {
                                setTitle("Instantiate hierarchy assumptions if possible (recommended).");
                                setSelected(temporarySettings.getPdSettings().useNullInstantiation);
                                return true;
                        }

                        @Override
                        public void eventChange() {
                                temporarySettings.getPdSettings().useNullInstantiation = isSelected();
                        }

                        @Override
                        public String getInfo() {
                                return "At the moment this option has only effect on hierarchy assumptions regarding the null object.\n"
                                                + "Example: Let A and B be classes.\n"
                                                + "If the option is not selected, the type null is treated as a normal class. "
                                                + "Consequently, the following assumptions are added:\n"
                                                + "\\forall x; (type_of_Null(x)->type_of_A(x))\n"
                                                + "\\forall x; (type_of_Null(x)->type_of_B(x))\n"
                                                + "If the option is selected, those assumptions are instantiated with a concrete null object:\n"
                                                + "type_of_A(null)\n"
                                                + "type_of_B(null)";
                        }
                }, new TableCheckBox() {
                        public boolean prepareValues() {
                                setTitle("Use built-in mechanism for uniqueness if possible.");
                                setSelected(temporarySettings.getPdSettings().useBuiltInUniqueness);
                                return true;
                        }

                        @Override
                        public void eventChange() {
                                temporarySettings.getPdSettings().useBuiltInUniqueness = isSelected();
                        }

                        @Override
                        public String getInfo() {
                                return "Some solvers support the uniqueness of functions by built-in mechanisms. If this option is selected "
                                                + "those mechanisms are used, otherwise some assumptions are added by using normal FOL.\n"
                                                + "Note: The uniqueness of functions is needed for translating attributes and arrays.";
                        }
                }, new TableCheckBox() {
                        public boolean prepareValues() {
                                setTitle("Use uninterpreted multiplication if necessary.");
                                setSelected(temporarySettings.getPdSettings().useUIMultiplication);
                                return true;
                        }

                        @Override
                        public void eventChange() {
                                temporarySettings.getPdSettings().useUIMultiplication = isSelected();
                        }

                        @Override
                        public String getInfo() {
                                return "Some solvers support only simple multiplications. For example Yices supports only multiplications of type a*b"
                                                + " where a or b must be a number.\n"
                                                + "In order to support more complex multiplications, this option can be activated: If the solver does not support a"
                                                + " certain kind of multiplication, the occurence of this multiplication is translated"
                                                + " into the uninterpreted function mult. Furthermore some"
                                                + " typical assumptions are added:\n"
                                                + "\\forall x; mult(x,0)=0\n"
                                                + "\\forall x; mult(0,x)=0\n"
                                                + "\\forall x; mult(x,1)=x\n"
                                                + "\\forall x; mult(1,x)=x\n"
                                                + "\\forall x; \\forall y; mult(x,y)=mult(y,x)\n"
                                                + "\\forall x; \\forall y; \\forall z; mult(mult(x,y),z)=mult(x,mult(y,z))\n"
                                                + "\\forall x; \\forall y; mult(x,y)=0 -> (x=0|y=0)\n"
                                                + "\\forall x; \\forall y; mult(x,y)=1 -> (x=1&y=1)\n"
                                                + "Note:\n"
                                                + "1. If this option is not selected, an exception is thrown in the case that a unsupported multiplication "
                                                + "occurs.\n"
                                                + "2. The translation makes the uninterpreted function mult unique, so that there cannot be any clashes with functions"
                                                + " that are introduced by the user.";
                        }
                }, new TableCheckBox() {
                        public boolean prepareValues() {

                                setTitle("Use uninterpreted constants for too small or too big numbers.");
                                setSelected(temporarySettings.getPdSettings().useConstantsForIntegers);
                                return true;
                        }

                        @Override
                        public void eventChange() {
                                temporarySettings.getPdSettings().useConstantsForIntegers = isSelected();
                        }

                        @Override
                        public String getInfo() {
                                return "Some solvers support only a certain interval of integers (e.g. Simplify). If this option is activated,"
                                                + " numbers that are not supported by the used solver are translated into uninterpreted constants. Furthermore "
                                                + " an asumption is added that states that the introduced constant is greater than the maximum of the supported numbers.\n\n"
                                                + "Example: Assume that a solver supports numbers less or equal 10:\n"
                                                + "The number 11 is translated into the constant c_11 and the assumption"
                                                + " c_11>10 is introduced.\n\n"
                                                + "Note: If this option is not selected, an exception is thrown in the case that a not supported number occurs.\n";
                        }
                }

                };
                return data;
        }

        private TableComponent[] getSolverData(final SolverType type) {
                TableComponent data[] = { new TableProperty(type) {

                        public boolean prepareValues() {
                                this.setTitle("Name:");
                                this.setValue(type.getName());
                                this.setEditable(false);
                                return true;
                        }

                        public void eventChange() {
                        }

                }, new TableProperty(type) {
                        public boolean prepareValues() {
                                this.setTitle("Installed:");

                                this.setValue(type.isInstalled(true));
                                this.setEditable(false);

                                return true;
                        }

                        public void eventChange() {
                        }

                        public String getInfo() {
                                return "There are two ways to make supported provers applicable for KeY:\n"
                                                + "1. Specify the absolute path of the prover in the field below.\n"
                                                + "2. Change the enviroment variable $PATH of your system, so that it "
                                                + "refers to the installed prover.";
                        }

                },

                new TableProperty(type) {

                        public boolean prepareValues() {
                                this.setTitle("Command:");
                                String command = temporarySettings.getPiSettings().getCommand(type);
                                this.setValue(command);
                                this.setEditable(true);
                                return true;
                        }

                        public void eventChange() {
                                temporarySettings.getPiSettings().setCommand(type, getValue());
                        }

                        @Override
                        public String getInfo() {
                                return "Editing the start command:\n"
                                                + "Specify the start command for an external procedure in such a way that it can be executed "
                                                + "to solve a problem file. Feel free to use any parameter to finetune the program.\n\n"
                                                + "Use %f as placeholder for the filename containing the problemdescription.\n\n"
                                                + "Use %p as placeholder for the problem directly. This should be needed in special cases only.";
                        }
                },

                new TableExplanation(type, "Information") {
                        public boolean visible() {
                                String info = type.getInfo();
                                return info != null && !info.isEmpty();
                        };

                        public boolean prepareValues() {
                                super.prepareValues();
                                String info = type.getInfo();

                                if (info == null || info.isEmpty()) {
                                        // Don't show the component if there is
                                        // no information
                                        // to present.
                                        return false;
                                }
                                init(info);
                                return true;
                        };
                }

                };
                return data;
        }

        private TableComponent[] getGeneralOptionsData() {
                TableComponent data[] = {

                                new TableCheckBox() {
                                        public boolean prepareValues() {
                                                setTitle("Show results in a dialog after executing the solvers.");
                                                setSelected(temporarySettings.getPiSettings().showResultsAfterExecution);
                                                return true;
                                        }

                                        @Override
                                        public void eventChange() {
                                                temporarySettings.getPiSettings().showResultsAfterExecution = isSelected();
                                        }

                                        @Override
                                        public String getInfo() {
                                                return "If you activate this option, a dialog "
                                                                + "will pop up showing results after executing the solvers.\n"
                                                                + "This dialog may help you to relate the results to the corresponding\n"
                                                                + "goals.";
                                        }
                                },

                                new TableSaveToFile() {

                                        public boolean prepareValues() {
                                                setTitle("Store translation to file:");
                                                setFolder(temporarySettings.getPiSettings().pathForSMTTranslation);
                                                setActivated(temporarySettings.getPiSettings().storeSMTTranslationToFile);
                                                return true;
                                        }

                                        public void eventChange() {
                                                temporarySettings.getPiSettings().pathForSMTTranslation = getFolder();
                                                temporarySettings.getPiSettings().storeSMTTranslationToFile = isActivated();
                                        }

                                        @Override
                                        public String getInfo() {
                                                return "Activate this option to store the translations "
                                                                + "that are handed over to the externals solvers:\n"
                                                                + "1. Choose the folder.\n"
                                                                + "2. Specify the filename:\n"
                                                                + "\t%s: the solver's name\n"
                                                                + "\t%d: date\n"
                                                                + "\t%t: time\n"
                                                                + "\t%i: the goal's number\n"
                                                                + "\n\n"
                                                                + "Example: /home/translations/%d_%t_%i_%s.txt"
                                                                + "\n\n"
                                                                + "Remark: After every restart of KeY this option "
                                                                + "is deactivated.";
                                        }

                                }

                                ,

                                new TableComboBox(
                                                temporarySettings.getPiSettings().modeOfProgressDialog,
                                                getProgressMode(temporarySettings.getPiSettings().PROGRESS_MODE_USER),
                                                getProgressMode(temporarySettings.getPiSettings().PROGRESS_MODE_CLOSE)) {

                                        public void eventChange() {
                                                temporarySettings.getPiSettings().modeOfProgressDialog = getSelectedItemIndex();
                                        }

                                        public boolean prepareValues() {
                                                setSelectedItem(temporarySettings.getPiSettings().modeOfProgressDialog);
                                                return true;
                                        }

                                        public String getInfo() {
                                                return "1. Option: The progress dialog remains open "
                                                                + "after executing the solvers so that the user "
                                                                + "can decide whether he wants to accept the results.\n"
                                                                + "\n"
                                                                + "2. Option: The progress dialog is closed once the "
                                                                + "external provers have done their work or the time limit "
                                                                + "has been exceeded.\n";// +
                                                // "\n"+
                                                // "3. Option: The progress dialog is closed once the first "
                                                // +
                                                // "external prover has successfully solved all given goals "
                                                // +
                                                // "or the time limit has been exceeded.";
                                        }

                                },

                                new TableProperty(this) {

                                        public void eventChange() {
                                                long value;
                                                try {
                                                        float val = Float
                                                                        .parseFloat(getValue());
                                                        value = (int) (val * 1000);
                                                } catch (NumberFormatException e) {
                                                        value = temporarySettings.getPiSettings().timeout;
                                                }
                                                temporarySettings.getPiSettings().timeout = value;

                                        }

                                        public boolean prepareValues() {
                                                setTitle("Timeout:");
                                                setValue(((float) temporarySettings.getPiSettings().timeout / 1000));
                                                return true;
                                        }

                                        public String getInfo() {
                                                return "Timeout for the external solvers in seconds. Fractions of a second are allowed.\n"
                                                                + "Example: 6.5";
                                        };

                                }, new TableProperty(this) {

                                        public void eventChange() {
                                                int value;
                                                try {
                                                        value = Integer
                                                                        .parseInt(getValue());
                                                } catch (NumberFormatException e) {
                                                        value = temporarySettings.getPiSettings().maxConcurrentProcesses;
                                                }
                                                temporarySettings.getPiSettings().maxConcurrentProcesses = value;

                                        }

                                        public boolean prepareValues() {
                                                setTitle("Concurrent Processes:");
                                                setValue(temporarySettings.getPiSettings().maxConcurrentProcesses);
                                                return true;
                                        }

                                        public String getInfo() {
                                                return "Maximal number or processes that are allowed to run concurrently.";
                                        };

                                }

                };

                return data;

        }

        private TableComponent[] getTacletOptionsData() {
                TableComponent data[] = {

                new TableSaveToFile() {

                        public boolean prepareValues() {
                                setFolder(temporarySettings.getPiSettings().pathForTacletTranslation);
                                setActivated(temporarySettings.getPiSettings().storeTacletTranslationToFile);
                                // enable(storeTacletsToFile);
                                setTitle("Store taclet translation to file:");
                                return true;
                        }

                        public void eventChange() {
                                temporarySettings.getPiSettings().pathForTacletTranslation = getFolder();
                                temporarySettings.getPiSettings().storeTacletTranslationToFile = isActivated();
                                // enable(isActivated());

                        }

                        @Override
                        public String getInfo() {
                                return "Activate this option to store the translations of taclets"
                                                + " that are handed over to the externals solvers:\n"
                                                + "1. Choose the folder.\n"
                                                + "2. Specify the filename:\n"
                                                + "\t%s: the solver's name\n"
                                                + "\t%d: date\n"
                                                + "\t%t: time\n"
                                                + "\t%i: the goal's number\n"
                                                + "\n\n"
                                                + "Example: ./home/translations/Taclet%d_%t_%i_%s.txt"
                                                + "\n\n"
                                                + "Note: After every restart of KeY this option"
                                                + " is deactivated.";
                        }
                }, new TableProperty(this) {
                        public void eventChange() {
                                int value;
                                try {
                                        value = Integer.parseInt(getValue());
                                } catch (NumberFormatException e) {
                                        value = temporarySettings.getPdSettings().maxGenericSorts;
                                }
                                temporarySettings.getPdSettings().maxGenericSorts = value;
                        }

                        public boolean prepareValues() {
                                setTitle("Maximum number of different generic sorts:");
                                setValue(temporarySettings.getPdSettings().maxGenericSorts);
                                return true;
                        };

                        public String getInfo() {
                                return "This option specifies how many different generic sorts are allowed"
                                                + " within a taclet.\n\n"
                                                + "Be aware of the fact that too many different generic sorts can"
                                                + " overwhelm the external solvers. On the other side there are taclets that"
                                                + " use a certain amount of different generic sorts (see: taclet selection).\n\n"
                                                + "Rule of thumb: Most of the taclets can be translated by using 2-3 different"
                                                + " generic sorts.";
                        }

                }

                };

                return data;

        }


        public ContentItem getDefaultItem() {
                return defaultItem;
        }

      
        public DefaultTreeModel getContent() {
           
                return getContentModel();
        }

}
