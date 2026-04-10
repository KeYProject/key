# key.util

This subproject contains various data structures and utility functions
used by the KeY project.

## Nullness checking

This subproject uses the EISOP branch of the Checker Framework
(https://eisop.github.io/) to check for nullness-related
errors at compile time.

Any use of a type is considered to be `@NonNull` by default unless `@Nullable`
is specified. E.g., a variable of type `@Nullable Object` cannot be assigned
to a variable of type `@NonNull Object`.

This is for the most part intuitive, but arrays and generics require some
explanation:
For an array, we specify the nullability of both the array and elements.
E.g., `@Nullable String @NonNull []` is a non-null array of nullable strings.
The nullability of a generic type is determined by its bounds. E.g., if we
have a class `class A<T extends @Nullable Object>`, then any use of `T` in `A`
is implicitly nullable; but if we have a class `class B<S>`, then any use of
`S` in `B` is implicitly non-null because this is the default bound.

For further details, see
https://jspecify.dev/docs/api/org/jspecify/annotations/package-summary.html
and
https://eisop.github.io/cf/manual/manual.html#nullness-checker

## Initialization checking

The Checker Framework also checks for initialization: If a constructor does
not initialize every `@NonNull` field with a non-null value, an error to that
effect is reported at compile time. If a constructor tries to call a non-helper
method, an error is also reported, as that method may rely on all `@NonNull`
fields being initialized.
You can mark a method as helper by specifying
`@UnderInitialization(InitClass.class) ReceiverClass this` as the first
parameter, where `ReceiverClass` is the name of the current class, and 
`InitClass` is the class up to which `this` should be initialized before
the method is allowed to be called.
If you want to allow the helper method being called even after `this` has been
further initialized, use `@UnknownInitialization(InitClass.class)` instead.
Within a helper method, all possibly uninitialized fields are considered
`@Nullable` even if declared as `@NonNull`.

E.g., consider the following listing.

```java
class A {
    @NonNull Object fieldA;
    
    A() {
        fieldA = new Object();
    }
}

class B extends A {
    @NonNull Object fieldB;
    
    B() {
        super();
        // Allowed because the super constructor has initialized this up to A
        helperA();

        // Not allowed because this is not yet initialized up to B
        helperB();
        
        fieldB = new Object();
        
        // Allowed now because fieldB was just initialized
        helperB();
        
        // Not allowed because B is not final; thus there may be a subclass
        // for which this has not yet been initialized.
        nonHelper();
    }
    
    void helperA(@UnderInitialization(A.class) B this) {
        // Allowed because this is initialized up to A;
        // thus fieldA is @NonNull
        fieldA.hashCode();
        // Not allowed because this is not initialized up to B;
        // thus fieldB is @Nullable
        fieldB.hashCode();
    }

    void helperB(@UnderInitialization(B.class) B this) {
        // Both allowed because this is initialized up to B
        fieldA.hashCode();
        fieldB.hashCode();
    }

    void nonHelper() {
        // ...
    }
}
```

The initialization types for arrays and generics are specified in the same way
as for nullness types.

For more details, see
https://eisop.github.io/cf/manual/manual.html#initialization-checker