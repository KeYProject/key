package org.key_project.key4eclipse.resources.counterexamples;

import de.uka.ilkd.key.smt.model.Model;


public class KeYProjectCounterExample {

    private String problemId;
    private String problemName;
    private KeYProjectCounterExampleModel model;
    
    public KeYProjectCounterExample(String id, String name, Model model){
        problemId = id;
        problemName = name;
        this.model = new KeYProjectCounterExampleModel(model); 
    }
    
    public KeYProjectCounterExample(String id, String name){
        problemId = id;
        problemName = name;
        this.model = new KeYProjectCounterExampleModel(); 
    }

    public String getProblemId() {
        return problemId;
    }

    public String getProblemName() {
        return problemName;
    }

    public KeYProjectCounterExampleModel getModel() {
        return model;
    }
    
    
}
