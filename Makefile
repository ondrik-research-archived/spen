BUILD_DIR=build
MAKE_FLAGS=-j 4
# no parallel CTest because of incremental minisat
# TEST_FLAGS=-j 50

.PHONY: all debug release doc clean test submodules-release submodules-debug

all:
	cd $(BUILD_DIR) && $(MAKE) $(MAKE_FLAGS) || echo "Type either \"make debug\" or \"make release\"!"

debug: submodules-debug
	cd $(BUILD_DIR) && cmake -DCMAKE_BUILD_TYPE=Debug .. && $(MAKE) $(MAKE_FLAGS)

release: submodules-release
	cd $(BUILD_DIR) && cmake -DCMAKE_BUILD_TYPE=Release .. && $(MAKE) $(MAKE_FLAGS)

doc:
	cd $(BUILD_DIR) && $(MAKE) $(MAKE_FLAGS) doc

test:
	cd $(BUILD_DIR) && ctest $(TEST_FLAGS)

clean:
	cd $(BUILD_DIR) && rm -rf *
	rm -rf html

submodules-release:
	git submodule init
	git submodule update
	cd libvata && $(MAKE) $(MAKE_FLAGS) release

submodules-debug:
	git submodule init
	git submodule update
	cd libvata && $(MAKE) $(MAKE_FLAGS) debug
