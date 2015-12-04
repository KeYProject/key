package org.key_project.key4eclipse.resources.counterexamples;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.gui.smt.CETree;
import de.uka.ilkd.key.smt.model.Heap;
import de.uka.ilkd.key.smt.model.LocationSet;
import de.uka.ilkd.key.smt.model.Model;
import de.uka.ilkd.key.smt.model.ObjectVal;
import de.uka.ilkd.key.smt.model.Sequence;
import de.uka.ilkd.key.util.Pair;

public class KeYProjectCounterExampleModel {

    private List<TreeElement> treeElements;
    
    public List<TreeElement> getTreeElements(){
        return treeElements;
    }
    
    public KeYProjectCounterExampleModel(Model model){
        treeElements = createTreeElementsFromModel(model);
    }
    
    public KeYProjectCounterExampleModel(){
        treeElements = new LinkedList<TreeElement>();
    }
    
    private void addTreeElement(List<TreeElement> treeElements, TreeElement t){
        if(t != null)
            treeElements.add(t);
    }
    
    public List<TreeElement> createTreeElementsFromModel(Model model){
        List<TreeElement> treeElements = new LinkedList<TreeElement>();
        addTreeElement(treeElements, createConstantsFromModel(model));
        addTreeElement(treeElements, createHeapsFromModel(model));
        addTreeElement(treeElements, createLocationSetsFromModel(model));
        addTreeElement(treeElements, createSequencesFromModel(model));
        return treeElements;
    }
    
    private TreeElement createConstantsFromModel(Model model){
        if(model == null || model.getConstants().isEmpty())
            return null;
        TreeElement constantsTreeElement = new TreeElement("Constants");
        List<Pair<String, String>> constantLabels = CETree.computeConstantLabels(model);
        for (Pair<String, String> pair : constantLabels) {
            constantsTreeElement.AddChild(new TreeElement(pair.first + "=" + pair.second));
        }
        return constantsTreeElement;
    }

    private TreeElement createHeapsFromModel(Model model) {
        if(model == null || model.getHeaps().isEmpty())
            return null;
        TreeElement heapsTreeElement = new TreeElement("Heaps");
        for(Heap h : model.getHeaps()){
            TreeElement heapTreeElement = new TreeElement(h.getName());
            for (ObjectVal o : h.getObjects()) {
                TreeElement objTreeElement = new TreeElement(o.getName());
                String sortName = CETree.computeSortName(o);
                for(Pair<String, String> pair : CETree.computeObjectProperties(o, sortName)){
                    objTreeElement.AddChild(new TreeElement(pair.first + "=" + pair.second));
                }
                List<Pair<String,String>> fields = CETree.computeFields(o);
                if(!fields.isEmpty()){
                    TreeElement fieldsTreeElement = new TreeElement("Fields");
                    for(Pair<String,String> pair : fields){
                        fieldsTreeElement.AddChild(new TreeElement(pair.first + "=" + pair.second));
                    }
                    objTreeElement.AddChild(fieldsTreeElement);
                }
                if(CETree.hasArrayFields(sortName)){
                    List<String> arrayFields = CETree.computeArrayFields(o);
                    TreeElement arrayFieldsTreeElement = new TreeElement("Array Fields");
                    for(String arrayField : arrayFields){
                        arrayFieldsTreeElement.AddChild(new TreeElement(arrayField));
                    }
                    objTreeElement.AddChild(arrayFieldsTreeElement);
                }
                List<Pair<String,String>> functions = CETree.computeFunctions(o);
                if(!functions.isEmpty()){
                    TreeElement functionsTreeElement = new TreeElement("Functions");
                    for(Pair<String,String> pair : functions){
                        functionsTreeElement.AddChild(new TreeElement(pair.first + "=" + pair.second));
                    }
                    objTreeElement.AddChild(functionsTreeElement);
                }
                
                heapTreeElement.AddChild(objTreeElement);
            }
            heapsTreeElement.AddChild(heapTreeElement);
        }
        
        
        return heapsTreeElement;
    }
    
    private TreeElement createLocationSetsFromModel(Model model){
        if(model == null || model.getLocsets().isEmpty())
            return null;
        TreeElement locSetsTreeElement = new TreeElement("Location Sets");
        for (LocationSet l : model.getLocsets()) {
            TreeElement locSetTreeElement = new TreeElement(CETree.computeLocationSetName(l));
            for (String p : CETree.computeLocationSetProperties(l)) {
                locSetTreeElement.AddChild(new TreeElement(p));
            }
            locSetsTreeElement.AddChild(locSetTreeElement);
        }
        return locSetsTreeElement;
    }
    
    private TreeElement createSequencesFromModel(Model model){
        if(model == null || model.getSequences().isEmpty())
            return null;
        TreeElement sequencesTreeElement = new TreeElement("Sequences");
        for (Sequence s : model.getSequences()) {
            TreeElement seqTreeElement = new TreeElement(CETree.computeSequenceName(s));
            for (String p : CETree.computeSequenceProperties(s)) {
                seqTreeElement.AddChild(new TreeElement(p));
            }
            sequencesTreeElement.AddChild(seqTreeElement);
        }
        return sequencesTreeElement;
    }
}
