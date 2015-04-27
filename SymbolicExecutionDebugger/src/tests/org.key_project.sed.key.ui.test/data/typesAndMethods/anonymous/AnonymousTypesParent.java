package anonymous;

import java.lang.annotation.Annotation;

import types.AAnnotation;
import types.AClass;
import types.AInterface;

public class AnonymousTypesParent {
	public void doSomething() {
		new AClass() {
			
		};
		
		new AInterface() {
			@Override
			public void methodInAInterface() {
				// TODO Auto-generated method stub
				
			}
		};
		
		new AAnnotation() {
			
			@Override
			public Class<? extends Annotation> annotationType() {
				return null;
			}
			
			@Override
			public String methodInAAnnotation() {
				return null;
			}
		};
	}
}
