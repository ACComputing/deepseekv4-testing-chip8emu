#!/usr/bin/env python3
"""
AC'S CHIP-8 EMULATOR
A Chip-8 interpreter with a dark mGBA-style GUI.
"""

import tkinter as tk
from tkinter import filedialog, messagebox
import sys
import os
import time
import random

# ------------------------- Chip-8 Core -------------------------
class Chip8:
    MEM_SIZE = 4096
    START_ADDR = 0x200
    FONTSET_SIZE = 80
    FONTSET = [
        0xF0, 0x90, 0x90, 0x90, 0xF0,  # 0
        0x20, 0x60, 0x20, 0x20, 0x70,  # 1
        0xF0, 0x10, 0xF0, 0x80, 0xF0,  # 2
        0xF0, 0x10, 0xF0, 0x10, 0xF0,  # 3
        0x90, 0x90, 0xF0, 0x10, 0x10,  # 4
        0xF0, 0x80, 0xF0, 0x10, 0xF0,  # 5
        0xF0, 0x80, 0xF0, 0x90, 0xF0,  # 6
        0xF0, 0x10, 0x20, 0x40, 0x40,  # 7
        0xF0, 0x90, 0xF0, 0x90, 0xF0,  # 8
        0xF0, 0x90, 0xF0, 0x10, 0xF0,  # 9
        0xF0, 0x90, 0xF0, 0x90, 0x90,  # A
        0xE0, 0x90, 0xE0, 0x90, 0xE0,  # B
        0xF0, 0x80, 0x80, 0x80, 0xF0,  # C
        0xE0, 0x90, 0x90, 0x90, 0xE0,  # D
        0xF0, 0x80, 0xF0, 0x80, 0xF0,  # E
        0xF0, 0x80, 0xF0, 0x80, 0x80   # F
    ]

    def __init__(self):
        self.memory = bytearray(self.MEM_SIZE)
        self.v = [0] * 16          # V0..VF
        self.i = 0                 # Index register
        self.pc = self.START_ADDR  # Program counter
        self.sp = 0                # Stack pointer
        self.stack = [0] * 16
        self.delay_timer = 0
        self.sound_timer = 0
        self.display = [0] * (64 * 32)  # 64x32 pixels
        self.keypad = [0] * 16          # key state (pressed=1)
        self.draw_flag = False
        self.running = True

        # Load fontset
        for i in range(self.FONTSET_SIZE):
            self.memory[i] = self.FONTSET[i]

        # Key mapping (physical keyboard -> Chip-8 key index)
        # 1 2 3 4      ->  1 2 3 C
        # Q W E R      ->  4 5 6 D
        # A S D F      ->  7 8 9 E
        # Z X C V      ->  A 0 B F
        self.key_map = {
            '1': 0x1, '2': 0x2, '3': 0x3, '4': 0xC,
            'q': 0x4, 'w': 0x5, 'e': 0x6, 'r': 0xD,
            'a': 0x7, 's': 0x8, 'd': 0x9, 'f': 0xE,
            'z': 0xA, 'x': 0x0, 'c': 0xB, 'v': 0xF
        }

    def load_rom(self, path):
        """Load ROM binary into memory starting at 0x200."""
        try:
            with open(path, 'rb') as f:
                rom_data = f.read()
            if len(rom_data) > self.MEM_SIZE - self.START_ADDR:
                raise ValueError("ROM too large")
            self.memory[self.START_ADDR:self.START_ADDR+len(rom_data)] = rom_data
            return True
        except Exception as e:
            print(f"Error loading ROM: {e}")
            return False

    def reset(self):
        """Reset CPU state, keep ROM loaded."""
        self.pc = self.START_ADDR
        self.i = 0
        self.sp = 0
        self.v = [0] * 16
        self.delay_timer = 0
        self.sound_timer = 0
        self.display = [0] * (64 * 32)
        self.draw_flag = False
        self.keypad = [0] * 16
        self.running = True

    def tick_timers(self):
        """Decrement timers at 60Hz."""
        if self.delay_timer > 0:
            self.delay_timer -= 1
        if self.sound_timer > 0:
            self.sound_timer -= 1
            if self.sound_timer == 0:
                # Beep would go here (platform dependent)
                pass

    def cycle(self):
        """Execute one CPU instruction."""
        if not self.running:
            return

        # Fetch opcode (big-endian)
        op = (self.memory[self.pc] << 8) | self.memory[self.pc + 1]
        self.pc += 2

        # Decode and execute
        x = (op & 0x0F00) >> 8
        y = (op & 0x00F0) >> 4
        nnn = op & 0x0FFF
        nn = op & 0x00FF
        n = op & 0x000F

        if op == 0x00E0:  # CLS
            self.display = [0] * (64 * 32)
            self.draw_flag = True
        elif op == 0x00EE:  # RET
            self.sp -= 1
            self.pc = self.stack[self.sp]
        elif op & 0xF000 == 0x1000:  # JP addr
            self.pc = nnn
        elif op & 0xF000 == 0x2000:  # CALL addr
            self.stack[self.sp] = self.pc
            self.sp += 1
            self.pc = nnn
        elif op & 0xF000 == 0x3000:  # SE Vx, byte
            if self.v[x] == nn:
                self.pc += 2
        elif op & 0xF000 == 0x4000:  # SNE Vx, byte
            if self.v[x] != nn:
                self.pc += 2
        elif op & 0xF000 == 0x5000:  # SE Vx, Vy
            if self.v[x] == self.v[y]:
                self.pc += 2
        elif op & 0xF000 == 0x6000:  # LD Vx, byte
            self.v[x] = nn
        elif op & 0xF000 == 0x7000:  # ADD Vx, byte
            self.v[x] = (self.v[x] + nn) & 0xFF
        elif op & 0xF000 == 0x8000:
            if n == 0x0:  # LD Vx, Vy
                self.v[x] = self.v[y]
            elif n == 0x1:  # OR Vx, Vy
                self.v[x] |= self.v[y]
                self.v[0xF] = 0  # quirk: some emus reset VF
            elif n == 0x2:  # AND Vx, Vy
                self.v[x] &= self.v[y]
                self.v[0xF] = 0
            elif n == 0x3:  # XOR Vx, Vy
                self.v[x] ^= self.v[y]
                self.v[0xF] = 0
            elif n == 0x4:  # ADD Vx, Vy
                result = self.v[x] + self.v[y]
                self.v[0xF] = 1 if result > 0xFF else 0
                self.v[x] = result & 0xFF
            elif n == 0x5:  # SUB Vx, Vy
                self.v[0xF] = 1 if self.v[x] >= self.v[y] else 0
                self.v[x] = (self.v[x] - self.v[y]) & 0xFF
            elif n == 0x6:  # SHR Vx {, Vy}
                self.v[0xF] = self.v[x] & 0x1
                self.v[x] >>= 1
            elif n == 0x7:  # SUBN Vx, Vy
                self.v[0xF] = 1 if self.v[y] >= self.v[x] else 0
                self.v[x] = (self.v[y] - self.v[x]) & 0xFF
            elif n == 0xE:  # SHL Vx {, Vy}
                self.v[0xF] = (self.v[x] & 0x80) >> 7
                self.v[x] = (self.v[x] << 1) & 0xFF
        elif op & 0xF000 == 0x9000:  # SNE Vx, Vy
            if self.v[x] != self.v[y]:
                self.pc += 2
        elif op & 0xF000 == 0xA000:  # LD I, addr
            self.i = nnn
        elif op & 0xF000 == 0xB000:  # JP V0, addr
            self.pc = (self.v[0] + nnn) & 0xFFF
        elif op & 0xF000 == 0xC000:  # RND Vx, byte
            self.v[x] = random.randint(0, 255) & nn
        elif op & 0xF000 == 0xD000:  # DRW Vx, Vy, nibble
            x_coord = self.v[x] & 0x3F
            y_coord = self.v[y] & 0x1F
            self.v[0xF] = 0
            for row in range(n):
                sprite_byte = self.memory[self.i + row]
                for col in range(8):
                    if (sprite_byte & (0x80 >> col)) != 0:
                        px = (x_coord + col) % 64
                        py = (y_coord + row) % 32
                        idx = py * 64 + px
                        if self.display[idx] == 1:
                            self.v[0xF] = 1
                        self.display[idx] ^= 1
            self.draw_flag = True
        elif op & 0xF000 == 0xE000:
            if nn == 0x9E:  # SKP Vx
                if self.keypad[self.v[x] & 0xF]:
                    self.pc += 2
            elif nn == 0xA1:  # SKNP Vx
                if not self.keypad[self.v[x] & 0xF]:
                    self.pc += 2
        elif op & 0xF000 == 0xF000:
            if nn == 0x07:  # LD Vx, DT
                self.v[x] = self.delay_timer
            elif nn == 0x0A:  # LD Vx, K
                # Wait for key press
                pressed = False
                for i in range(16):
                    if self.keypad[i]:
                        self.v[x] = i
                        pressed = True
                        break
                if not pressed:
                    self.pc -= 2  # retry instruction
            elif nn == 0x15:  # LD DT, Vx
                self.delay_timer = self.v[x]
            elif nn == 0x18:  # LD ST, Vx
                self.sound_timer = self.v[x]
            elif nn == 0x1E:  # ADD I, Vx
                self.i = (self.i + self.v[x]) & 0xFFF
            elif nn == 0x29:  # LD F, Vx
                self.i = (self.v[x] & 0xF) * 5
            elif nn == 0x33:  # LD B, Vx
                val = self.v[x]
                self.memory[self.i] = val // 100
                self.memory[self.i + 1] = (val // 10) % 10
                self.memory[self.i + 2] = val % 10
            elif nn == 0x55:  # LD [I], Vx
                for reg in range(x + 1):
                    self.memory[self.i + reg] = self.v[reg]
                # self.i += x + 1  (original behavior, often disabled)
            elif nn == 0x65:  # LD Vx, [I]
                for reg in range(x + 1):
                    self.v[reg] = self.memory[self.i + reg]
                # self.i += x + 1
        else:
            print(f"Unknown opcode: {op:04X} at PC={self.pc-2:04X}")

    def key_down(self, key_char):
        """Set keypad state based on pressed character."""
        key_char = key_char.lower()
        if key_char in self.key_map:
            self.keypad[self.key_map[key_char]] = 1

    def key_up(self, key_char):
        """Clear keypad state."""
        key_char = key_char.lower()
        if key_char in self.key_map:
            self.keypad[self.key_map[key_char]] = 0


# ------------------------- GUI (mGBA style) -------------------------
class Chip8GUI:
    SCALE = 10  # each Chip-8 pixel becomes 10x10 on screen
    WIDTH = 64 * SCALE
    HEIGHT = 32 * SCALE

    def __init__(self, root):
        self.root = root
        root.title("AC'S CHIP-8 EMULATOR")
        root.geometry("600x400")  # initial size, will expand to fit canvas
        root.resizable(False, False)

        # mGBA dark theme colors
        self.bg_color = "#1e1e1e"
        self.fg_color = "#d4d4d4"
        self.accent_color = "#007acc"
        self.canvas_bg = "#000000"
        self.pixel_on = "#33ff33"   # retro green
        self.pixel_off = "#0a0a0a"

        root.configure(bg=self.bg_color)

        # Menu bar
        menubar = tk.Menu(root)
        file_menu = tk.Menu(menubar, tearoff=0)
        file_menu.add_command(label="Open ROM...", command=self.open_rom)
        file_menu.add_command(label="Reset", command=self.reset_emu)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=root.quit)
        menubar.add_cascade(label="File", menu=file_menu)
        root.config(menu=menubar)

        # Main frame
        main_frame = tk.Frame(root, bg=self.bg_color)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        # Canvas for display
        self.canvas = tk.Canvas(
            main_frame,
            width=self.WIDTH,
            height=self.HEIGHT,
            bg=self.canvas_bg,
            highlightthickness=0
        )
        self.canvas.pack(pady=(0, 10))

        # Status bar
        self.status_var = tk.StringVar()
        self.status_var.set("No ROM loaded")
        status_label = tk.Label(
            main_frame,
            textvariable=self.status_var,
            bg=self.bg_color,
            fg=self.fg_color,
            anchor=tk.W
        )
        status_label.pack(fill=tk.X)

        # Button frame
        btn_frame = tk.Frame(main_frame, bg=self.bg_color)
        btn_frame.pack(pady=(10, 0))

        self.run_btn = tk.Button(
            btn_frame,
            text="Run",
            command=self.toggle_run,
            bg=self.accent_color,
            fg="white",
            activebackground="#005a9e",
            width=8
        )
        self.run_btn.pack(side=tk.LEFT, padx=5)

        self.step_btn = tk.Button(
            btn_frame,
            text="Step",
            command=self.step,
            bg="#3c3c3c",
            fg=self.fg_color,
            activebackground="#505050",
            width=8
        )
        self.step_btn.pack(side=tk.LEFT, padx=5)

        self.reset_btn = tk.Button(
            btn_frame,
            text="Reset",
            command=self.reset_emu,
            bg="#3c3c3c",
            fg=self.fg_color,
            activebackground="#505050",
            width=8
        )
        self.reset_btn.pack(side=tk.LEFT, padx=5)

        # Chip-8 instance
        self.chip8 = Chip8()
        self.rom_loaded = False
        self.emulation_running = False
        self.after_id = None

        # Bind keyboard events
        root.bind('<KeyPress>', self.on_key_down)
        root.bind('<KeyRelease>', self.on_key_up)

        # Initial draw
        self.update_display()

    def open_rom(self):
        """Load a Chip-8 ROM file."""
        file_path = filedialog.askopenfilename(
            title="Open Chip-8 ROM",
            filetypes=[("Chip-8 ROMs", "*.ch8 *.c8 *.rom"), ("All Files", "*.*")]
        )
        if file_path:
            if self.chip8.load_rom(file_path):
                self.rom_loaded = True
                self.chip8.reset()
                self.status_var.set(f"Loaded: {os.path.basename(file_path)}")
                self.update_display()
                self.start_emulation()
            else:
                messagebox.showerror("Error", "Failed to load ROM file.")

    def reset_emu(self):
        """Reset the emulator (keep ROM)."""
        if self.rom_loaded:
            self.chip8.reset()
            self.update_display()
            self.status_var.set("Reset")
            if not self.emulation_running:
                self.start_emulation()

    def toggle_run(self):
        """Pause or resume emulation."""
        if not self.rom_loaded:
            return
        if self.emulation_running:
            self.emulation_running = False
            self.run_btn.config(text="Run")
            if self.after_id:
                self.root.after_cancel(self.after_id)
                self.after_id = None
        else:
            self.start_emulation()

    def start_emulation(self):
        """Start the emulation loop."""
        if self.rom_loaded and not self.emulation_running:
            self.emulation_running = True
            self.run_btn.config(text="Pause")
            self.run_loop()

    def run_loop(self):
        """Execute cycles at ~500Hz and update timers at 60Hz."""
        if not self.emulation_running:
            return

        # Execute ~8 instructions per frame to get ~500 instructions/sec
        for _ in range(8):
            self.chip8.cycle()

        # Timers at 60Hz (16.6ms) - we call tick_timers once per loop iteration
        self.chip8.tick_timers()

        # Beep if sound timer active (simple console beep)
        if self.chip8.sound_timer > 0:
            # On Windows, try to beep; otherwise ignore
            if sys.platform == "win32":
                import winsound
                winsound.Beep(800, 30)
            else:
                print('\a', end='', flush=True)  # terminal bell

        if self.chip8.draw_flag:
            self.update_display()
            self.chip8.draw_flag = False

        self.after_id = self.root.after(16, self.run_loop)  # ~60 FPS

    def step(self):
        """Execute one instruction and update display if needed."""
        if not self.rom_loaded:
            return
        self.chip8.cycle()
        if self.chip8.draw_flag:
            self.update_display()
            self.chip8.draw_flag = False

    def update_display(self):
        """Draw the Chip-8 display on the canvas."""
        self.canvas.delete("all")
        for y in range(32):
            for x in range(64):
                pixel = self.chip8.display[y * 64 + x]
                color = self.pixel_on if pixel else self.pixel_off
                x1 = x * self.SCALE
                y1 = y * self.SCALE
                x2 = x1 + self.SCALE
                y2 = y1 + self.SCALE
                self.canvas.create_rectangle(x1, y1, x2, y2, fill=color, outline="")

    def on_key_down(self, event):
        """Handle key press."""
        if event.char:
            self.chip8.key_down(event.char)

    def on_key_up(self, event):
        """Handle key release."""
        if event.char:
            self.chip8.key_up(event.char)


if __name__ == "__main__":
    root = tk.Tk()
    app = Chip8GUI(root)
    root.mainloop()