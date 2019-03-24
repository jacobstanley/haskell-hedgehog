HEADERS = circularbuffer.h
OBJECTS = circularbuffer.o

default: circularbuffer.dylib

%.o: %.c $(HEADERS)
	gcc -c $< -o $@

circularbuffer.dylib: $(OBJECTS)
	gcc -dynamiclib -dy $(OBJECTS) -o $@

clean:
	-rm -f $(OBJECTS)
	-rm -f circularbuffer.dylib
