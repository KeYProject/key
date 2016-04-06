package org.key_project.sed.example.model;

import java.io.InputStream;
import java.io.OutputStream;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.runtime.PlatformObject;
import org.eclipse.debug.core.DebugEvent;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IProcess;
import org.eclipse.debug.core.model.IStreamsProxy;

/**
 * An {@link IProcess} implementation for stuff running in the current JVM
 * which is needed to offer the console.
 * @author Martin Hentschel
 */
public class SameJVMProcess extends PlatformObject implements IProcess {
   /**
    * The {@link ILaunch} this {@link IProcess} is contained in.
    */
   private final ILaunch launch;
   
   /**
    * The name of this {@link IProcess}.
    */
   private final String name;
   
   /**
    * Table of client defined attributes
    */
   private final Map<String, String> attributes = new HashMap<String, String>();
   
   /**
    * The used {@link IStreamsProxy}.
    */
   private final IStreamsProxy streamsProxy;
   
   /**
    * The terminated status.
    */
   private boolean terminated = false;
   
   /**
    * Constructor.
    * @param launch The {@link ILaunch} the new {@link IProcess} is contained in. 
    * @param name The name of the new {@link IProcess}.
    */
   public SameJVMProcess(ILaunch launch, String name) {
      this(launch, name, null, null, null);
   }
   
   /**
    * Constructor.
    * @param launch The {@link ILaunch} the new {@link IProcess} is contained in. 
    * @param name The name of the new {@link IProcess}.
    * @param out The {@link InputStream} from which the output should be read.
    * @param errOut The {@link InputStream} from which the error output should be read.
    * @param in The {@link OutputStream} to write input to.
    */
   public SameJVMProcess(ILaunch launch, 
                         String name, 
                         InputStream out, 
                         InputStream errOut, 
                         OutputStream in) {
      assert launch != null;
      assert name != null;
      this.launch = launch;
      this.name = name;
      this.streamsProxy = out != null || errOut != null || in != null ? 
                          new CustomStreamsProxy(out, errOut, in) : 
                          null;
      fireCreationEvent();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ILaunch getLaunch() {
      return launch;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canTerminate() {
      return true;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isTerminated() {
      return terminated;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getExitValue() throws DebugException {
      return 0;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void terminate() throws DebugException {
      if (!terminated) {
         terminated = true;
         if (streamsProxy instanceof CustomStreamsProxy) {
            CustomStreamsProxy csp = (CustomStreamsProxy) streamsProxy;
            csp.close();
            csp.kill();
         }
         fireTerminateEvent();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getLabel() {
      return name;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getAttribute(String key) {
      return attributes.get(key);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setAttribute(String key, String value) {
      String oldValue = getAttribute(key);
      if (oldValue == null || !oldValue.equals(value)) {
         attributes.put(key, value);
         fireChangeEvent();
      }
   }

   /**
    * Fires a creation event.
    */
   protected void fireCreationEvent() {
      fireEvent(new DebugEvent(this, DebugEvent.CREATE));
   }

   /**
    * Fires a change event.
    */
   protected void fireChangeEvent() {
      fireEvent(new DebugEvent(this, DebugEvent.CHANGE));
   }

   /**
    * Fires a terminate event.
    */
   protected void fireTerminateEvent() {
      fireEvent(new DebugEvent(this, DebugEvent.TERMINATE));
   }

   /**
    * Fires the given debug event.
    * @param event debug event to fire
    */
   protected void fireEvent(DebugEvent event) {
      DebugPlugin manager = DebugPlugin.getDefault();
      if (manager != null) {
         manager.fireDebugEventSet(new DebugEvent[]{event});
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IStreamsProxy getStreamsProxy() {
      return streamsProxy;
   }
}
