

package cpu

import spinal.core._
import spinal.lib._

import vexriscv.plugin._
import vexriscv.{plugin, VexRiscv, VexRiscvConfig}

import spinal.core._
import spinal.lib._
import spinal.lib.bus.simple._
import spinal.lib.com.jtag.Jtag

import scala.collection.mutable.ArrayBuffer
import vexriscv.plugin.{NONE, _}
import vexriscv.{VexRiscv, VexRiscvConfig, plugin}

case class VexRiscvWithDebug() extends Component
{
    val io = new Bundle {
        val iBus                    = master(IBusSimpleBus(null))
        val dBus                    = master(DBusSimpleBus())
        val timerInterrupt          = in(Bool)
        val externalInterrupt       = in(Bool)
        val jtag                    = slave(Jtag())
    }

    // Configure a reasonable performance VexRiscv with compressed instructions.
    // Different kinds of exceptions are enabled  (illegal access, address
    // misalignment) because it makes sense to do that when you have a debugger
    // connected...

    val config = VexRiscvConfig(
        plugins = List(
            new IBusSimplePlugin(
                resetVector = 0x00000000l,
                cmdForkOnSecondStage    = false,
                cmdForkPersistence      = false,
                prediction              = STATIC,
                // Only useful when the IBus can issue an error.
                catchAccessFault        = false,    
                compressedGen           = true
            ),
            new DBusSimplePlugin(
                // Trap when a load or store access is misaligned.
                catchAddressMisaligned  = true,     
                catchAccessFault        = false
            ),
            new CsrPlugin(
                CsrPluginConfig(
                    // Trap when accessing a priviledged CSR from non-priviledged mode. Or when
                    // there are MRET or SRET instructions during non-priviledged mode. And other CSR
                    // related errors.
                    catchIllegalAccess  = true,
                    mvendorid           = null,
                    marchid             = null,
                    mimpid              = null,
                    mhartid             = null,
                    misaExtensionsInit  = 66,
                    misaAccess          = CsrAccess.NONE,
                    mtvecAccess         = CsrAccess.NONE,
                    mtvecInit           = 0x00000020,
                    mepcAccess          = CsrAccess.READ_WRITE,
                    mscratchGen         = false,
                    mcauseAccess        = CsrAccess.READ_ONLY,
                    mbadaddrAccess      = CsrAccess.READ_ONLY,    // == mtvalAccess
                    mcycleAccess        = CsrAccess.NONE,
                    minstretAccess      = CsrAccess.NONE,
                    ecallGen            = false,
                    ebreakGen           = true,
                    wfiGenAsWait        = false,
                    ucycleAccess        = CsrAccess.READ_ONLY,
                    uinstretAccess      = CsrAccess.NONE
                )
            ),
            new DecoderSimplePlugin(
                catchIllegalInstruction = false
            ),
            new RegFilePlugin(
                regFileReadyKind        = plugin.SYNC,
                zeroBoot                = false
            ),
            new IntAluPlugin,
            new SrcPlugin(
                separatedAddSub         = false,
                executeInsertion        = false
            ),
            new LightShifterPlugin,
            new HazardSimplePlugin(
                bypassExecute           = true,
                bypassMemory            = true,
                bypassWriteBack         = true,
                bypassWriteBackBuffer   = true,
                pessimisticUseSrc       = false,
                pessimisticWriteRegFile = false,
                pessimisticAddressMatch = false
            ),
            new BranchPlugin(
                earlyBranch             = false,
                catchAddressMisaligned  = false
            ),
            new DebugPlugin(ClockDomain.current),
            new YamlPlugin("VexRiscvWithDebug.yaml")
        )
    )

    // Instantiate the CPU
    val cpu = new VexRiscv(config)

    // Map the busses of the cpu to external IO ports of this module.
    for(plugin <- cpu.plugins) plugin match{
        case plugin : IBusSimplePlugin  =>  io.iBus               <> plugin.iBus
        case plugin : DBusSimplePlugin  =>  io.dBus               <> plugin.dBus
        case plugin : CsrPlugin     => { 
                                            io.timerInterrupt     <> plugin.timerInterrupt
                                            io.externalInterrupt  <> plugin.externalInterrupt
                                       }
        case plugin : DebugPlugin   => plugin.debugClockDomain { 
                                            io.jtag               <> plugin.io.bus.fromJtag() 
                                       }
        case _ =>
    }
    
}

object VexRiscvWithDebug {
    def main(args: Array[String]) {

        val config = SpinalConfig(anonymSignalUniqueness = true)
        config.generateVerilog({
            val toplevel = new VexRiscvWithDebug()
            toplevel
        })
    }
}

