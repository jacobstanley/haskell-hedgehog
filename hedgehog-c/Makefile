HEADERS = test.h
OBJECTS = test.o

default: test.dylib

%.o: %.c $(HEADERS)
	gcc -c $< -o $@

test.dylib: $(OBJECTS)
	gcc -dynamiclib -dy $(OBJECTS) -o $@

clean:
	-rm -f $(OBJECTS)
	-rm -f test.dylib
