package de.uka.ilkd.key.util.removegenerics.monitor;

public class ConsoleGenericRemoverMonitor implements GenericRemoverMonitor {
   @Override
   public void taskStarted(String message) {
       System.out.println(message);
   }

   @Override
   public void warningOccurred(String message) {
       System.out.println(message);
   }
}
