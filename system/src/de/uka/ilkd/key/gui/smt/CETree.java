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

package de.uka.ilkd.key.gui.smt;

import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import javax.swing.JTree;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreePath;

import de.uka.ilkd.key.smt.model.Heap;
import de.uka.ilkd.key.smt.model.Location;
import de.uka.ilkd.key.smt.model.LocationSet;
import de.uka.ilkd.key.smt.model.Model;
import de.uka.ilkd.key.smt.model.ObjectVal;
import de.uka.ilkd.key.smt.model.Sequence;

public class CETree {

    /**
     * A comparator that sort ignoRiNG cASe.
     * Used to sort labels.
     */
    private static final Comparator<? super String> IGNORECASE_COMPARATOR =
            new Comparator<String>() {
        public int compare(String o1, String o2) {
            return o1.compareToIgnoreCase(o2);
        }
    };

	/**
	 * The JTree to be shown.
	 */
	private JTree tree;
	/**
	 * The SMT model.
	 */
	private Model model;





	public CETree(Model model) {
		super();
		this.model = model;
		model.removeUnnecessaryObjects();
		model.addAliases();		
		initTree();
	}

	private void initTree(){		
		tree = new JTree();		
		DefaultMutableTreeNode root = constructTree();		
		DefaultTreeModel tm = new DefaultTreeModel(root);		
		tree.setModel(tm);
		CEMouseAdapter adapter = new CEMouseAdapter();
		tree.addMouseListener(adapter);
//		this.setLayout(new BorderLayout());
//		this.add(tree, BorderLayout.CENTER);
	}

    public JTree getTreeComponent() {
        return tree;
    };


	private DefaultMutableTreeNode constructTree(){
		DefaultMutableTreeNode root = new DefaultMutableTreeNode("Model");

		DefaultMutableTreeNode constants = new DefaultMutableTreeNode("Constants");
		fillConstants(constants);
		root.add(constants);
		DefaultMutableTreeNode heaps = new DefaultMutableTreeNode("Heaps");
		fillHeaps(heaps);
		root.add(heaps);
		DefaultMutableTreeNode locssets = new DefaultMutableTreeNode("Location Sets");
		fillLocsets(locssets);
		root.add(locssets);
		DefaultMutableTreeNode sequences = new DefaultMutableTreeNode("Sequences");
		fillSequences(sequences);
		root.add(sequences);
		return root;
	}

	private void fillHeaps(DefaultMutableTreeNode heaps) {

		for(Heap h : model.getHeaps()){
			DefaultMutableTreeNode heap = new DefaultMutableTreeNode(h.getName());
			heaps.add(heap);
			for(ObjectVal ov :h.getObjects()){
				DefaultMutableTreeNode object = new DefaultMutableTreeNode(ov.getName());
				heap.add(object);

				addObjectProperties(ov, object);				
			}			
		}		
	}

	/**
	 * @param ov
	 * @param object
	 */
	private void addObjectProperties(ObjectVal ov,
			DefaultMutableTreeNode object) {
		//Type			
		String sortName = ov.getSort() == null ? "java.lang.Object" : ov.getSort().name().toString();
		sortName = Model.removePipes(sortName);
		DefaultMutableTreeNode sort = new DefaultMutableTreeNode("Type="+sortName);								
//		DefaultMutableTreeNode sortValue = new DefaultMutableTreeNode(sortName);
//		sort.add(sortValue);
		object.add(sort);

		//Exact Instance				
		boolean ei = ov.isExactInstance();
		DefaultMutableTreeNode exactInstance = new DefaultMutableTreeNode("Exact Instance="+ei);
//		DefaultMutableTreeNode exactInstanceValue = new DefaultMutableTreeNode(ei);
//		exactInstance.add(exactInstanceValue);
		object.add(exactInstance);	

		//Length				
		int l = ov.getLength();
		DefaultMutableTreeNode length = new DefaultMutableTreeNode("Length="+l);
//		DefaultMutableTreeNode lengthValue = new DefaultMutableTreeNode(l);
//		length.add(lengthValue);
		object.add(length);	

		//Fields
		DefaultMutableTreeNode fields = new DefaultMutableTreeNode("Fields");
		object.add(fields);
        List<String> labels = new ArrayList<String>();

        for(Entry<String,String> e : ov.getFieldvalues().entrySet()) {
            labels.add(Model.removePipes(e.getKey())+"="+e.getValue());
        }

        // sort the labels alphabetically
        Collections.sort(labels, IGNORECASE_COMPARATOR);

        for(String label : labels){
            DefaultMutableTreeNode name = new DefaultMutableTreeNode(label);
            fields.add(name);
		}

		//Array Fields
		if(sortName.endsWith("[]")){
			DefaultMutableTreeNode arrayFields = new DefaultMutableTreeNode("Array Fields");
			object.add(arrayFields);
			for(int i = 0; i< ov.getLength(); ++i){					
				DefaultMutableTreeNode arrayField = new DefaultMutableTreeNode("["+i+"]="+ov.getArrayValue(i));
				//DefaultMutableTreeNode arrayFieldValue = new DefaultMutableTreeNode(ov.getArrayValue(i));
				//arrayField.add(arrayFieldValue);
				arrayFields.add(arrayField);					
			}
		}


		//Fun Values
		DefaultMutableTreeNode functionValues = new DefaultMutableTreeNode("Functions");
		object.add(functionValues);
		for(Entry<String,String> e : ov.getFunValues().entrySet()){
			DefaultMutableTreeNode fun = new DefaultMutableTreeNode(Model.removePipes(e.getKey())+"="+e.getValue());
			//DefaultMutableTreeNode funValue =  new DefaultMutableTreeNode(e.getValue());
			//fun.add(funValue);
			functionValues.add(fun);
		}
	}

	private void fillLocsets(DefaultMutableTreeNode locsets){
		for(LocationSet ls : model.getLocsets()){
			DefaultMutableTreeNode locset = new DefaultMutableTreeNode(Model.removePipes(ls.getName()));
			locsets.add(locset);
			addLocSetProperties(ls, locset);		
		}
	}

	/**
	 * @param ls
	 * @param locset
	 */
	private void addLocSetProperties(LocationSet ls,
			DefaultMutableTreeNode locset) {
		for(int i = 0; i< ls.size(); ++i){
			Location l = ls.get(i);
			String locationName = "("+Model.removePipes(l.getObjectID())+", "+Model.removePipes(l.getFieldID())+")";
			DefaultMutableTreeNode locationNode = new DefaultMutableTreeNode(locationName);
			locset.add(locationNode);
		}
	}

	private void fillSequences(DefaultMutableTreeNode sequences){

		for(Sequence s : model.getSequences()){
			DefaultMutableTreeNode sequence = new DefaultMutableTreeNode(Model.removePipes(s.getName()));
			sequences.add(sequence);
			addSequenceProperties(s, sequence);
		}


	}

	/**
	 * @param s
	 * @param sequence
	 */
	private void addSequenceProperties(Sequence s,
			DefaultMutableTreeNode sequence) {
		DefaultMutableTreeNode length = new DefaultMutableTreeNode("Length="+s.getLength());
//		DefaultMutableTreeNode lengthValue = new DefaultMutableTreeNode(s.getLength());
//		length.add(lengthValue);
		sequence.add(length);

		for(int i = 0; i < s.getLength(); ++i){

			DefaultMutableTreeNode arrField = new DefaultMutableTreeNode("["+i+"]="+Model.removePipes(s.get(i)));
			//			DefaultMutableTreeNode arrValue = new DefaultMutableTreeNode(s.get(i));
			//			arrField.add(arrValue);
			sequence.add(arrField);

		}
	}

	private void fillConstants(DefaultMutableTreeNode constants) {

		Map<String, String> map = model.getConstants();
        List<String> labels = new ArrayList<String>();

        for(Entry<String,String> e : map.entrySet()) {
            labels.add(Model.removePipes(e.getKey())+"="+e.getValue());
        }

        // sort the labels alphabetically
        Collections.sort(labels, IGNORECASE_COMPARATOR);

        for(String label : labels){
            DefaultMutableTreeNode name = new DefaultMutableTreeNode(label);
			constants.add(name);
		}

	}

	private class CEMouseAdapter extends MouseAdapter {





		public CEMouseAdapter() {
			super();

		}



		public void mousePressed(MouseEvent e) {
			int selRow = tree.getRowForLocation(e.getX(), e.getY());
			TreePath selPath = tree.getPathForLocation(e.getX(), e.getY());
			if(selRow != -1) {	            
				if(e.getClickCount() == 2) {
					Object oNode = selPath.getLastPathComponent();
					if(oNode instanceof DefaultMutableTreeNode){
						DefaultMutableTreeNode node = (DefaultMutableTreeNode) oNode;

						if(node.getChildCount()>0){
							return;
						}

						String value = node.getUserObject().toString();
						if(value.contains("="))
							value = value.substring(value.indexOf('=')+1);
						
						//System.err.println("Expand: "+value);

						if(value.startsWith("#o")){

							value = value.substring(value.indexOf('=')+1);

							DefaultMutableTreeNode secondNode = (DefaultMutableTreeNode) selPath.getPath()[1];
							if(secondNode.getUserObject().toString().equals("Heaps")){
								DefaultMutableTreeNode heapNode = (DefaultMutableTreeNode) selPath.getPath()[2];
								String heapID = heapNode.getUserObject().toString();

								//search for heap
								Heap heap = null;
								for(Heap h : model.getHeaps()){
									if(heapID.equals(h.getName())){
										heap = h;
										break;
									}
								}								
								if(heap == null) return;


								//search for object
								ObjectVal val = null;
								for(ObjectVal o : heap.getObjects()){
									if(o.getName().equals(value)){
										val = o;
										break;
									}
								}								
								if(val ==null) return;								
								addObjectProperties(val, node);

							}


						}
						else if(value.startsWith("#l")){
							LocationSet locset = null;
							for(LocationSet ls : model.getLocsets()){								
								if(ls.getName().startsWith(value)){									
									locset = ls;
									break;
								}								
							}
							if(locset ==null){
								return;							
							}
							addLocSetProperties(locset, node);

						}
						else if(value.startsWith("#s")){

							Sequence sequence = null;
							for(Sequence s : model.getSequences()){
								if(s.getName().startsWith(value)){									
									sequence = s;
									break;
								}
							}
							if(sequence == null){								
								return;
							}

							addSequenceProperties(sequence, node);


						}

						tree.expandPath(selPath);



					}

				}
			}
		}
        }

}