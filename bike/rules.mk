OBJ_FILES += $(patsubst %.S, $(OBJ_DIR)/%.o, $(SSRC))
OBJ_FILES += $(patsubst %.c, $(OBJ_DIR)/%.o, $(CSRC))

all: $(OBJ_FILES)

$(OBJ_DIR)/%.o: %.c $(OBJ_DIR)
	$(CC) $(CFLAGS) -c -o $@ $<

$(OBJ_DIR)/%.o: FromNIST/%.c $(OBJ_DIR)
	$(CC) $(CFLAGS) -c -o $@ $<

$(OBJ_DIR)/%.o: %.S $(OBJ_DIR)
	$(CC) $(CFLAGS) -c -o $@ $<
