// Allocate a heap size of 1024 bytes
var heapBuffer = new ArrayBuffer(1024);

// We want 64-bit words
var HEAP = new Float64Array(heapBuffer);

var allocPointer = 0;

module.exports = {
  mref: function (index) {
    return HEAD[index];
  },

  mset: function (index, value) {
    HEAP[index] = value;
  },

  alloc: function (numWords) {
    var p = allocPointer;
    allocPointer += numWords;
    return p;
  }
};
