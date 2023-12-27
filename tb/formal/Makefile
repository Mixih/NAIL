# defs
SBY := sby

ALL_TARGETS :=

# utils
define create_fv_rules
$(1)_prove: $(1).sby $(2)
	$$(SBY) -f $$< prove
$(1)_cover: $(1).sby $(2)
	$$(SBY) -f $$< cover
ALL_TARGETS += $(1)_prove
ALL_TARGETS += $(1)_cover
endef

# targets
.DEFAULT_GOAL := all

ARGMAX_SRCS := ../../hdl/arith/argmax.v ../../hdl/util/util.vh
$(eval $(call create_fv_rules,argmax,$(ARGMAX_SRCS)))

INT_BAUD_GEN_SRCS := ../../hdl/util/int_baud_gen.v ../../hdl/util/util.vh
$(eval $(call create_fv_rules,int_baud_gen,$(INT_BAUD_GEN_SRCS)))

MUL32X32_SRCS := ../../hdl/arith/mul32x32.v ../../hdl/util/util.vh
$(eval $(call create_fv_rules,mul32x32,$(MUL32_32_SRCS)))

SEVEN_SEG_SRCS := ../../hdl/hmi/seven_seg.v ../../hdl/util/int_baud_gen.v ../../hdl/util/util.vh
$(eval $(call create_fv_rules,seven_seg,$(SEVEN_SEG_SRCS)))

UART_TX_LL_8N1_SRCS := ../../hdl/serdes/uart_tx_ll_8n1.v ../../hdl/util/int_baud_gen.v ../../hdl/util/util.vh
$(eval $(call create_fv_rules,uart_tx_ll_8n1,$(UART_TX_LL_8N1_SRCS)))

UART_RX_LL_8N1_SRCS := ../../hdl/serdes/uart_rx_ll_8n1.v ../../hdl/util/int_baud_gen.v ../../hdl/util/util.vh
$(eval $(call create_fv_rules,uart_rx_ll_8n1,$(UART_RX_LL_8N1_SRCS)))

SYNC_FIFO_KEEP_SRCS := ../../hdl/dataplane/sync_fifo.v ../../hdl/util/util.vh
$(eval $(call create_fv_rules,sync_fifo_keep,$(SYNC_FIFO_KEEP_SRCS)))

SYNC_FIFO_OVERWRITE_SRCS := ../../hdl/dataplane/sync_fifo.v ../../hdl/util/util.vh
$(eval $(call create_fv_rules,sync_fifo_overwrite,$(SYNC_FIFO_OVERWRITE_SRCS)))

.PHONY: all
all: $(ALL_TARGETS)

.PHONY: clean
clean:
	rm -rf *_cover *_prove
