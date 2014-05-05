package de.uka.ilkd.key.gui.testgen;

import java.io.File;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.Properties;

import de.uka.ilkd.key.gui.GUIEvent;
import de.uka.ilkd.key.gui.configuration.Settings;
import de.uka.ilkd.key.gui.configuration.SettingsConverter;
import de.uka.ilkd.key.gui.configuration.SettingsListener;
import de.uka.ilkd.key.testgen.TestGenSettings;

public class TestGenerationSettings implements TestGenSettings, Settings,
Cloneable {

	//Default Values for option fields
	private static final int DEFAULT_MAXUNWINDS = 3;

	private static final int DEFAULT_CONCURRENTPROCESSES = 1;

	private static final String DEFAULT_OUTPUTPATH = System.getProperty("user.home") + File.separator + "testFiles";

	private static final boolean DEFAULT_REMOVEDUPLICATES = true;

	private static final boolean DEFAULT_USEJUNIT = false;

	private static final boolean DEFAULT_INVARIANTFORALL = true;

	//Option fields
	private int maxUnwinds;

	private String outputPath;

	private boolean removeDuplicates;

	private boolean useJunit;

	private int concurrentProcesses;

	private boolean invariantForAll;

	private Collection<SettingsListener> listeners;

	//Property name

	private static final String propMaxUwinds = "[TestGenSettings]maxUnwinds";
	private static final String propOutputPath = "[TestGenSettings]OutputPath";
	private static final String propRemoveDuplicates = "[TestGenSettings]RemoveDuplicates";
	private static final String propUseJUnit = "[TestGenSettings]UseJUnit";
	private static final String propConcurrentProcesses = "[TestGenSettings]ConcurrentProcesses";
	private static final String propInvariantForAll = "[TestGenSettings]InvariantForAll";




	public TestGenerationSettings() {
		listeners = new LinkedHashSet<SettingsListener>();
		maxUnwinds = DEFAULT_MAXUNWINDS;
		outputPath = DEFAULT_OUTPUTPATH;
		removeDuplicates = DEFAULT_REMOVEDUPLICATES;
		useJunit = DEFAULT_USEJUNIT;
		concurrentProcesses = DEFAULT_CONCURRENTPROCESSES;
		invariantForAll = DEFAULT_INVARIANTFORALL;
	}

	public TestGenerationSettings(TestGenerationSettings data){
		listeners = new LinkedHashSet<SettingsListener>();
		for(SettingsListener l : data.listeners){
			listeners.add(l);
		}

		maxUnwinds = data.maxUnwinds;
		outputPath = data.outputPath;
		removeDuplicates = data.removeDuplicates;
		useJunit = data.useJunit;
		concurrentProcesses = data.concurrentProcesses;
		invariantForAll = data.invariantForAll;
	}

	@Override
	public void readSettings(Object sender, Properties props) {
		maxUnwinds = SettingsConverter.read(props, propMaxUwinds, DEFAULT_MAXUNWINDS);
		outputPath = SettingsConverter.read(props, propOutputPath, DEFAULT_OUTPUTPATH);
		removeDuplicates = SettingsConverter.read(props, propRemoveDuplicates, DEFAULT_REMOVEDUPLICATES);
		useJunit = SettingsConverter.read(props, propUseJUnit, DEFAULT_USEJUNIT);
		concurrentProcesses = SettingsConverter.read(props, propConcurrentProcesses, DEFAULT_CONCURRENTPROCESSES);
		invariantForAll = SettingsConverter.read(props, propInvariantForAll, DEFAULT_INVARIANTFORALL);
	}

	@Override
	public void writeSettings(Object sender, Properties props) {
		SettingsConverter.store(props, propConcurrentProcesses, DEFAULT_CONCURRENTPROCESSES);
		SettingsConverter.store(props, propInvariantForAll, DEFAULT_INVARIANTFORALL);
		SettingsConverter.store(props, propMaxUwinds, DEFAULT_MAXUNWINDS);
		SettingsConverter.store(props, propOutputPath, DEFAULT_OUTPUTPATH);
		SettingsConverter.store(props, propRemoveDuplicates, DEFAULT_REMOVEDUPLICATES);
		SettingsConverter.store(props, propUseJUnit, DEFAULT_USEJUNIT);		
	}

	public TestGenerationSettings clone(TestGenerationSettings data){

		return new TestGenerationSettings(data);

	}

	@Override
	public void addSettingsListener(SettingsListener l) {
		listeners.add(l);
	}

	@Override
	public int getMaximalUnwinds() {
		return this.maxUnwinds;
	}	

	@Override
	public boolean removeDuplicates() {
		return this.removeDuplicates;
	}

	@Override
	public boolean useJunit() {
		return this.useJunit;
	}

	@Override
	public int getNumberOfProcesses() {
		return this.concurrentProcesses;
	}

	@Override
	public String getOutputFolderPath() {
		return this.outputPath;
	}

	@Override
	public boolean invaraiantForAll() {
		return invariantForAll;
	}	

	public void setMaxUnwinds(int maxUnwinds) {
		this.maxUnwinds = maxUnwinds;
	}

	public void setOutputPath(String outputPath) {
		this.outputPath = outputPath;
	}

	public void setRemoveDuplicates(boolean removeDuplicates) {
		this.removeDuplicates = removeDuplicates;
	}

	public void setUseJunit(boolean useJunit) {
		this.useJunit = useJunit;
	}

	public void setConcurrentProcesses(int concurrentProcesses) {
		this.concurrentProcesses = concurrentProcesses;
	}

	public void setInvariantForAll(boolean invariantForAll) {
		this.invariantForAll = invariantForAll;
	}

	public void fireSettingsChanged() {
		for (SettingsListener aListenerList : listeners) {
			aListenerList.settingsChanged(new GUIEvent(this));
		}

	}
}
