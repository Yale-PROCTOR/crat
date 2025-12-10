SRCS = $(wildcard *.c)
OBJS = $(SRCS:.c=.o)
TARGET = sum

all: $(TARGET)

$(TARGET): $(OBJS)
	$(CC) $(OBJS) -o $@

clean:
	rm -f *.o $(TARGET)
